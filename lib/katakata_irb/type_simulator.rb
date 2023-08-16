require 'ripper'
require 'set'
require_relative 'types'
require_relative 'scope'
require 'yarp'

class KatakataIrb::TypeSimulator
  class DigTarget
    def initialize(parents, receiver, &block)
      @dig_ids = parents.to_h { [_1.__id__, true] }
      @target_id = receiver.__id__
      @block = block
    end

    def dig?(node) = @dig_ids[node.__id__]
    def target?(node) = @target_id == node.__id__
    def resolve(type, scope)
      @block.call type, scope
    end
  end

  module LexerElemMatcher
    refine Ripper::Lexer::Elem do
      def deconstruct_keys(_keys)
        {
          tok: tok,
          event: event,
          label: state.allbits?(Ripper::EXPR_LABEL),
          beg: state.allbits?(Ripper::EXPR_BEG),
          dot: state.allbits?(Ripper::EXPR_DOT)
        }
      end
    end
  end
  using LexerElemMatcher

  OBJECT_METHODS = {
    to_s: KatakataIrb::Types::STRING,
    to_str: KatakataIrb::Types::STRING,
    to_a: KatakataIrb::Types::ARRAY,
    to_ary: KatakataIrb::Types::ARRAY,
    to_h: KatakataIrb::Types::HASH,
    to_hash: KatakataIrb::Types::HASH,
    to_i: KatakataIrb::Types::INTEGER,
    to_int: KatakataIrb::Types::INTEGER,
    to_f: KatakataIrb::Types::FLOAT,
    to_c: KatakataIrb::Types::COMPLEX,
    to_r: KatakataIrb::Types::RATIONAL
  }

  def initialize(dig_targets)
    @dig_targets = dig_targets
  end

  def simulate_evaluate(node, scope, case_target: nil)
    result = simulate_evaluate_inner(node, scope, case_target: case_target)
    @dig_targets.resolve result, scope if @dig_targets.target?(node)
    result
  end

  def simulate_evaluate_inner(node, scope, case_target: nil)
    case node
    when YARP::ProgramNode
      simulate_evaluate node.statements, scope
    when YARP::StatementsNode
      if node.body.empty?
        KatakataIrb::NIL
      else
        node.body.map { simulate_evaluate _1, scope }.last
      end
    when YARP::DefNode
      sexp in [:def, _method_name_exp, params, body_stmt]
      sexp in [:defs, receiver_exp, _dot_exp, _method_name_exp, params, body_stmt]
      if receiver_exp
        receiver_exp in [:paren, receiver_exp]
        self_type = simulate_evaluate receiver_exp, scope
      else
        current_self_types = scope.self_type.types
        self_types = current_self_types.map do |type|
          if type.is_a?(KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
            KatakataIrb::Types::InstanceType.new type.module_or_class
          else
            type
          end
        end
        self_type = KatakataIrb::Types::UnionType[*self_types]
      end
      if @dig_targets.dig? sexp
        params in [:paren, params]
        params ||= [:params, nil, nil, nil, nil, nil, nil, nil] # params might be nil in ruby 3.0
        params_table = extract_param_names(params).to_h { [_1, KatakataIrb::Types::NIL] }
        method_scope = KatakataIrb::Scope.new(
          scope,
          { **params_table, KatakataIrb::Scope::SELF => self_type, KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil },
          trace_lvar: false
        )
        evaluate_assign_params params, [], method_scope
        method_scope.conditional { evaluate_param_defaults params, _1 }
        simulate_evaluate body_stmt, method_scope
        method_scope.merge_jumps
        scope.update method_scope
      end
      KatakataIrb::Types::SYMBOL
    when YARP::IntegerNode
      KatakataIrb::Types::INTEGER
    when YARP::FloatNode
      KatakataIrb::Types::FLOAT
    when YARP::RationalNode
      KatakataIrb::Types::RATIONAL
    when YARP::ImaginaryNode
      KatakataIrb::Types::COMPLEX
    when YARP::StringNode
      KatakataIrb::Types::STRING
    when YARP::XStringNode
      KatakataIrb::Types::UnionType[KatakataIrb::Types::STRING, KatakataIrb::Types::NIL]
    when YARP::SymbolNode
      KatakataIrb::Types::SYMBOL
    when YARP::RegularExpressionNode
      KatakataIrb::Types::REGEXP
    when YARP::InterpolatedStringNode
      node.parts.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::STRING
    when YARP::InterpolatedXStringNode
      node.parts.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::STRING
    when YARP::InterpolatedSymbolNode
      node.parts.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::SYMBOL
    when YARP::InterpolatedRegularExpressionNode
      node.parts.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::STRING
    when YARP::EmbeddedStatementsNode
      node.statements ? simulate_evaluate(node.statements, scope) : KatakataIrb::Types::NIL
      KatakataIrb::Types::STRING
    when YARP::ArrayNode
      types = node.elements.map do |elem|
        if elem.is_a? YARP::SplatNode
          splat = simulate_evaluate elem.expression, scope
          array_elem, non_array = partition_to_array splat.nonnillable, :to_a
          KatakataIrb::Types::UnionType[*array_elem, *non_array]
        else
          simulate_evaluate elem, scope
        end
      end
      KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*types]
    when YARP::HashNode, YARP::KeywordHashNode
      keys = []
      values = []
      node.elements.each do |assoc|
        case assoc.is_a?
        when YARP::AssocNode
          keys << simulate_evaluate(assoc.key, scope)
          values << simulate_evaluate(assoc.value, scope)
        when YARP::AssocSplatNode
          hash = simulate_evaluate assoc.value, scope
          unless hash.is_a?(KatakataIrb::Types::InstanceType) && hash.klass == Hash
            hash = simulate_call hash, :to_hash, [], nil, nil
          end
          if hash.is_a?(KatakataIrb::Types::InstanceType) && hash.klass == Hash
            keys << hash.params[:K] if hash.params[:K]
            values << hash.params[:V] if hash.params[:V]
          end
        end
      end
      if keys.empty? && values.empty?
        KatakataIrb::Types::InstanceType.new Hash
      else
        KatakataIrb::Types::InstanceType.new Hash, K: KatakataIrb::Types::UnionType[*keys], V: KatakataIrb::Types::UnionType[*values]
      end
    when YARP::ParenthesesNode
      node.statements ? simulate_evaluate(node.statements, scope) : KatakataIrb::Types::NIL
    when YARP::ConstantPathNode
      name = node.child.slice
      return KatakataIrb::BaseScope.type_of { Object.const_get name } if node.parent.nil?
      receiver = simulate_evaluate node.parent, scope
      receiver.is_a?(KatakataIrb::Types::SingletonType) ? KatakataIrb::BaseScope.type_of { receiver.module_or_class.const_get name } : KatakataIrb::Types::NIL
    when YARP::SelfNode
      scope.self_type
    when YARP::TrueNode
      KatakataIrb::Types::TRUE
    when YARP::FalseNode
      KatakataIrb::Types::FALSE
    when YARP::NilNode
      KatakataIrb::Types::NIL
    when YARP::SourceFileNode
        KatakataIrb::Types::STRING
    when YARP::SourceLineNode
        KatakataIrb::Types::INTEGER
    when YARP::SourceEncodingNode
      KatakataIrb::Types::InstanceType.new Encoding
    when YARP::LocalVariableReadNode
      scope[node.constant_id] || KatakataIrb::Types::NIL
    when YARP::ConstantReadNode, YARP::GlobalVariableReadNode, YARP::InstanceVariableReadNode, YARP::ClassVariableReadNode
      scope[node.slice] || KatakataIrb::Types::NIL
    when YARP::CallNode
      if node.receiver.nil? && node.message == 'raise'
        scope.terminate_with KatakataIrb::Scope::RAISE_BREAK, KatakataIrb::Types::TRUE
        return KatakataIrb::Types::NIL
      end
      receiver_type = node.receiver ? simulate_evaluate(node.receiver, scope) : scope.self_type
      evaluate_method = lambda do |scope|
        arguments = node.arguments&.arguments&.dup || []
        block_arg = arguments.pop.expression if arguments.last.is_a? YARP::BlockArgumentNode
        kwargs = arguments.pop.elements if arguments.last.is_a?(YARP::KeywordHashNode)
        args_type = arguments.map do |arg|
          if arg.is_a? YARP::SplatNode
            simulate_evaluate arg, scope
            nil # TODO: splat
          else
            simulate_evaluate arg, scope
          end
        end
        if kwargs
          kwargs_type = kwargs.map do |arg|
            case arg
            when YARP::AssocNode
              if arg.key.is_a?(SymbolNode)
                [arg.key.value, simulate_evaluate(arg.value, scope)]
              else
                simulate_evaluate arg.key, scope
                simulate_evaluate arg.value, scope
                nil
              end
            when YARP::AssocSplatNode
              simulate_evaluate assoc.value, scope
              nil
            end
          end.compact.to_h
        end
        if block_arg.is_a? YARP::SymbolNode
          block_sym = block_arg.value
        elsif block_arg
          simulate_evaluate block_arg, scope
        end

        if block_sym
          call_block_proc = ->(block_args, _self_type) do
            block_receiver, *rest = block_args
            block_receiver ? simulate_call(block_receiver || KatakataIrb::Types::OBJECT, block_sym, rest, nil, nil) : KatakataIrb::Types::OBJECT
          end
        elsif node.block
          call_block_proc = ->(block_args, block_self_type) do
            scope.conditional do |s|
              if params
                names = extract_param_names(params)
              else
                names = (1..max_numbered_params(body)).map { "_#{_1}" }
                params = [:params, names.map { [:@ident, _1, [0, 0]] }, nil, nil, nil, nil, nil, nil]
              end
              params_table = names.zip(block_args).to_h { [_1, _2 || KatakataIrb::Types::NIL] }
              table = { **params_table, KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil }
              table[KatakataIrb::Scope::SELF] = block_self_type if block_self_type
              block_scope = KatakataIrb::Scope.new s, table
              evaluate_assign_params params, block_args, block_scope
              block_scope.conditional { evaluate_param_defaults params, _1 } if params
              if type == :do_block
                result = simulate_evaluate body, block_scope
              else
                result = body.map { simulate_evaluate _1, block_scope }.last
              end
              block_scope.merge_jumps
              s.update block_scope
              nexts = block_scope[KatakataIrb::Scope::NEXT_RESULT]
              breaks = block_scope[KatakataIrb::Scope::BREAK_RESULT]
              if block_scope.terminated?
                [KatakataIrb::Types::UnionType[*nexts], breaks]
              else
                [KatakataIrb::Types::UnionType[result, *nexts], breaks]
              end
            end
          end
        else
          call_block_proc = ->(_block_args, _self_type) { KatakataIrb::Types::OBJECT }
        end
        simulate_call receiver_type, node.message, args_type, kwargs_type, call_block_proc
      end
      if node.operator == '&.'
        result = scope.conditional { evaluate_method.call _1 }
        if receiver_type.nillable?
          KatakataIrb::Types::UnionType[result, KatakataIrb::Types::NIL]
        else
          result
        end
      else
        evaluate_method.call scope
      end
    when YARP::AndNode
      simulate_evaluate node.left, scope
      right = scope.conditional { simulate_evaluate node.right, _1 }
      KatakataIrb::Types::UnionType[right, KatakataIrb::Types::NIL, KatakataIrb::Types::FALSE]
    when YARP::OrNode
      left = simulate_evaluate node.left, scope
      right = scope.conditional { simulate_evaluate node.right, _1 }
      KatakataIrb::Types::UnionType[left, right]
    when %[:lambda, params, statements]
      params in [:paren, params] # ->{}, -> do end
      statements in [:bodystmt, statements, _unknown, _unknown, _unknown] # -> do end
      params in [:paren, params]
      params_table = extract_param_names(params).to_h { [_1, KatakataIrb::Types::NIL] }
      block_scope = KatakataIrb::Scope.new scope, { **params_table, KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }
      block_scope.conditional do |s|
        evaluate_assign_params params, [], s
        s.conditional { evaluate_param_defaults params, _1 }
        statements.each { simulate_evaluate _1, s }
      end
      block_scope.merge_jumps
      scope.update block_scope
      KatakataIrb::Types::ProcType.new
    when %[:assign, [:var_field, [:@gvar | :@ivar | :@cvar | :@ident | :@const, name,]], value]
      res = simulate_evaluate value, scope
      scope[name] = res
      res
    when %[:assign, [:aref_field, receiver, key], value]
      simulate_evaluate receiver, scope
      args, kwargs, _block = retrieve_method_args key
      args.each do |arg|
        item = arg.is_a?(KatakataIrb::Types::Splat) ? arg.item : arg
        simulate_evaluate item, scope
      end
      kwargs_type kwargs, scope
      simulate_evaluate value, scope
    when %[:assign, [:field, receiver, period, [:@ident,]], value]
      simulate_evaluate receiver, scope
      if period in [:@op, '&.',]
        scope.conditional { simulate_evaluate value, scope }
      else
        simulate_evaluate value, scope
      end
    when %[:assign, target, value]
      simulate_evaluate target, scope
      simulate_evaluate value, scope
    when %[:massign, targets, value]
      targets in [:mlhs, *targets] # (a,b) = value
      rhs = simulate_evaluate value, scope
      evaluate_massign targets, rhs, scope
      rhs
    when %[:mrhs_new_from_args | :mrhs_add_star,]
      values, = evaluate_mrhs sexp, scope
      KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*values]
    when %[:ifop, cond, tval, fval]
      simulate_evaluate cond, scope
      KatakataIrb::Types::UnionType[*scope.run_branches(
        -> { simulate_evaluate tval, _1 },
        -> { simulate_evaluate fval, _1 }
      )]
    when %[:if_mod | :unless_mod, cond, statement]
      simulate_evaluate cond, scope
      KatakataIrb::Types::UnionType[scope.conditional { simulate_evaluate statement, _1 }, KatakataIrb::Types::NIL]
    when %[:if | :unless | :elsif, cond, statements, else_statement]
      simulate_evaluate cond, scope
      results = scope.run_branches(
        ->(s) { statements.map { simulate_evaluate _1, s }.last },
        ->(s) { else_statement ? simulate_evaluate(else_statement, s) : KatakataIrb::Types::NIL }
      )
      results.empty? ? KatakataIrb::Types::NIL : KatakataIrb::Types::UnionType[*results]
    when %[:while | :until, cond, statements]
      inner_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::BREAK_RESULT => nil }, passthrough: true
      simulate_evaluate cond, inner_scope
      inner_scope.conditional { |s| statements.each { simulate_evaluate _1, s } }
      inner_scope.merge_jumps
      scope.update inner_scope
      breaks = inner_scope[KatakataIrb::Scope::BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, KatakataIrb::Types::NIL] : KatakataIrb::Types::NIL
    when %[:while_mod | :until_mod, cond, statement]
      inner_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::BREAK_RESULT => nil }, passthrough: true
      simulate_evaluate cond, inner_scope
      inner_scope.conditional { |s| simulate_evaluate statement, s }
      inner_scope.merge_jumps
      scope.update inner_scope
      breaks = inner_scope[KatakataIrb::Scope::BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, KatakataIrb::Types::NIL] : KatakataIrb::Types::NIL
    when %[:break | :next | :return => jump_type, value]
      internal_key = jump_type == :break ? KatakataIrb::Scope::BREAK_RESULT : jump_type == :next ? KatakataIrb::Scope::NEXT_RESULT : KatakataIrb::Scope::RETURN_RESULT
      if value.empty?
        jump_value = KatakataIrb::Types::NIL
      else
        values, kw = evaluate_mrhs value, scope
        values << kw if kw
        jump_value = values.size == 1 ? values.first : KatakataIrb::Types::InstanceType.new(Array, Elem: KatakataIrb::Types::UnionType[*values])
      end
      scope.terminate_with internal_key, jump_value
      KatakataIrb::Types::NIL
    when %[:return0]
      scope.terminate_with KatakataIrb::Scope::RETURN_RESULT, KatakataIrb::Types::NIL
      KatakataIrb::Types::NIL
    when %[:yield, args]
      evaluate_mrhs args, scope
      KatakataIrb::Types::OBJECT
    when %[:yield0]
      KatakataIrb::Types::OBJECT
    when %[:redo | :retry]
      scope.terminate
    when %[:zsuper]
      KatakataIrb::Types::OBJECT
    when %[:super, args]
      args, kwargs, _block = retrieve_method_args args
      args.each do |arg|
        item = arg.is_a?(KatakataIrb::Types::Splat) ? arg.item : arg
        simulate_evaluate item, scope
      end
      kwargs_type kwargs, scope
      KatakataIrb::Types::OBJECT
    when YARP::BeginNode
      rescue_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::RAISE_BREAK => nil }, passthrough: true if node.rescue_clause
      return_type = node.statements ? simulate_evaluate(node.statements, rescue_scope || scope) : KatakataIrb::Types::NIL
      if node.rescue_clause
        rescue_scope.merge_jumps
        scope.update rescue_scope
        rescue_return_type = scope.run_branches(
          ->{ simulate_evaluate node.rescue_clause, _1 },
          ->{ simulate_evaluate node.else_clause, _1 if node.else_clause }
        )
        return_type = KatakataIrb::Types::UnionType[return_type, rescue_return_type]
      end
      simulate_evaluate node.ensure_clause, scope if node.ensure_clause
      return_type
    when YARP::RescueNode
      return_type = scope.conditional do |s|
        if node.reference
          error_classes = node.exceptions.flat_map do |e|
            if e.is_a? YARP::SplatNode
              splat = simulate_evaluate e.expression, s
              array_elem, non_array = partition_to_array splat.nonnillable, :to_a
              [*array_elem, *non_array]
            else
              simulate_evaluate e, s
            end
          end.uniq
          error_types = error_classes.filter_map { KatakataIrb::Types::InstanceType.new _1.module_or_class if _1.is_a?(KatakataIrb::Types::SingletonType) }
          error_types << KatakataIrb::Types::InstanceType.new(StandardError) if error_types.empty?
          s[node.reference.constant_id] = KatakataIrb::Types::UnionType[*error_types]
        end
        node.statements ? simulate_evaluate(node.statements, s) : KatakataIrb::Types::NIL
      end
      if node.consequent # begin; rescue A; rescue B; end
        KatakataIrb::Types::UnionType[return_type, scope.conditional { simulate_evaluate node.consequent, _1 }]
      else
        return_type
      end
    when YARP::RescueModifierNode
      rescue_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::RAISE_BREAK => nil }, passthrough: true
      a = simulate_evaluate node.expression, rescue_scope
      rescue_scope.merge_jumps
      scope.update rescue_scope
      b = scope.conditional { simulate_evaluate node.rescue_expression, _1 }
      KatakataIrb::Types::UnionType[a, b]
    when YARP::ModuleNode #[:module, module_stmt, body_stmt]
      module_types = simulate_evaluate(module_stmt, scope).types.grep(KatakataIrb::Types::SingletonType)
      module_types << KatakataIrb::Types::MODULE if module_types.empty?
      module_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::SELF => KatakataIrb::Types::UnionType[*module_types], KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
      result = simulate_evaluate body_stmt, module_scope
      scope.update module_scope
      result
    when YARP::SingletonClassNode # [:sclass, klass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope).types.filter_map do |type|
        KatakataIrb::Types::SingletonType.new type.klass if type.is_a? KatakataIrb::Types::InstanceType
      end
      klass_types = [KatakataIrb::Types::CLASS] if klass_types.empty?
      sclass_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::SELF => KatakataIrb::Types::UnionType[*klass_types], KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
      result = simulate_evaluate body_stmt, sclass_scope
      scope.update sclass_scope
      result
    when YARP::ClassNode # [:class, klass_stmt, superclass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope).types
      klass_types += simulate_evaluate(superclass_stmt, scope).types if superclass_stmt
      klass_types = klass_types.select do |type|
        type.is_a?(KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
      end
      klass_types << KatakataIrb::Types::CLASS if klass_types.empty?
      klass_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::SELF => KatakataIrb::Types::UnionType[*klass_types], KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
      result = simulate_evaluate body_stmt, klass_scope
      scope.update klass_scope
      result
    when YARP::ForNode # [:for, fields, enum, statements]
      fields = [fields] if fields in [:var_field | :field | :aref_field,]
      params = [:params, fields, nil, nil, nil, nil, nil, nil]
      enum = simulate_evaluate enum, scope
      extract_param_names(params).each { scope[_1] = KatakataIrb::Types::NIL }
      response = simulate_call enum, :first, [], nil, nil
      evaluate_assign_params params, [response], scope
      inner_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::BREAK_RESULT => nil }, passthrough: true
      scope.conditional do |s|
        statements.each { simulate_evaluate _1, s }
      end
      inner_scope.merge_jumps
      scope.update inner_scope
      breaks = inner_scope[KatakataIrb::Scope::BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, enum] : enum
    when YARP::CaseNode # [:case, target_exp, match_exp]
      target = target_exp ? simulate_evaluate(target_exp, scope) : KatakataIrb::Types::NIL
      simulate_evaluate match_exp, scope, case_target: target
    when YARP::WhenNode # in [:when, pattern, if_statements, else_statement]
      eval_pattern = lambda do |s, pattern, *rest|
        simulate_evaluate pattern, s
        scope.conditional { eval_pattern.call(_1, *rest) } if rest.any?
      end
      if_branch = lambda do |s|
        eval_pattern.call(s, *pattern)
        if_statements.map { simulate_evaluate _1, s }.last
      end
      else_branch = lambda do |s|
        pattern.each { simulate_evaluate _1, s }
        simulate_evaluate(else_statement, s, case_target: case_target)
      end
      if if_statements && else_statement
        KatakataIrb::Types::UnionType[*scope.run_branches(if_branch, else_branch)]
      else
        KatakataIrb::Types::UnionType[scope.conditional { (if_branch || else_branch).call _1 }, KatakataIrb::Types::NIL]
      end
    when YARP::InNode
    when YARP::MatchRequiredNode, YARP::MatchPredicateNode
      if node in [:in, [:var_field, [:@ident, name,]], if_statements, else_statement]
        scope.never { simulate_evaluate else_statement, scope } if else_statement
        scope[name] = case_target || KatakataIrb::Types::OBJECT
        if_statements ? if_statements.map { simulate_evaluate _1, scope }.last : KatakataIrb::Types::NIL
      elsif node in [:in, pattern, if_statements, else_statement]
        pattern_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::PATTERNMATCH_BREAK => nil }, passthrough: true)
        results = pattern_scope.run_branches(
          ->(s) {
            match_pattern case_target, pattern, s
            if_statements ? if_statements.map { simulate_evaluate _1, s }.last : KatakataIrb::Types::NIL
          },
          ->(s) {
            else_statement ? simulate_evaluate(else_statement, s, case_target: case_target) : KatakataIrb::Types::NIL
          }
        )
        pattern_scope.merge_jumps
        scope.update pattern_scope
        KatakataIrb::Types::UnionType[*results]
      end
    when YARP::RangeNode
      beg_type = simulate_evaluate node.left, scope if range_beg
      end_type = simulate_evaluate node.right, scope if range_end
      elem = (KatakataIrb::Types::UnionType[*[beg_type, end_type].compact]).nonnillable
      KatakataIrb::Types::InstanceType.new Range, { Elem: elem }
    when YARP::DefinedNode
      scope.conditional { simulate_evaluate node.value, _1 }
      KatakataIrb::Types::UnionType[KatakataIrb::Types::STRING, KatakataIrb::Types::NIL]
    else
      KatakataIrb.log_puts
      KatakataIrb.log_puts :NOMATCH
      KatakataIrb.log_puts node.inspect
      KatakataIrb::Types::NIL
    end
  end

  def match_pattern(target, pattern, scope)
    breakable = -> { scope.terminate_with KatakataIrb::Scope::PATTERNMATCH_BREAK, KatakataIrb::Types::NIL }
    types = target.types
    case pattern
    in [:var_field, [:@ident, name,]]
      scope[name] = target
    in [:var_ref,] # in Array, in ^a, in nil
    in [:@int | :@float | :@rational | :@imaginary | :@CHAR | :symbol_literal | :string_literal | :regexp_literal,]
    in [:begin, statement] # in (statement)
      simulate_evaluate statement, scope
      breakable.call
    in [:binary, lpattern, :|, rpattern]
      match_pattern target, lpattern, scope
      scope.conditional { match_pattern target, rpattern, _1 }
      breakable.call
    in [:binary, lpattern, :'=>', [:var_field, [:@ident, name,]] => rpattern]
      if lpattern in [:var_ref, [:@const, _const_name,]]
        const_value = simulate_evaluate lpattern, scope
        if const_value.is_a?(KatakataIrb::Types::SingletonType) && const_value.module_or_class.is_a?(Class)
          scope[name] = KatakataIrb::Types::InstanceType.new const_value.module_or_class
        else
          scope[name] = KatakataIrb::Types::OBJECT
        end
        breakable.call
      else
        match_pattern target, lpattern, scope
        match_pattern target, rpattern, scope
      end
    in [:aryptn, _unknown, items, splat, post_items]
      # TODO: deconstruct keys
      array_types = types.select { _1.is_a?(KatakataIrb::Types::InstanceType) && _1.klass == Array }
      elem = KatakataIrb::Types::UnionType[*array_types.filter_map { _1.params[:Elem] }]
      items&.each do |item|
        match_pattern elem, item, scope
      end
      if splat in [:var_field, [:@ident, name,]]
        scope[name] = KatakataIrb::Types::InstanceType.new Array, Elem: elem
        breakable.call
      end
      post_items&.each do |item|
        match_pattern elem, item, scope
      end
    in [:hshptn, _unknown, items, splat]
      # TODO: deconstruct keys
      hash_types = types.select { _1.is_a?(KatakataIrb::Types::InstanceType) && _1.klass == Hash }
      key_type = KatakataIrb::Types::UnionType[*hash_types.filter_map { _1.params[:K] }]
      value_type = KatakataIrb::Types::UnionType[*hash_types.filter_map { _1.params[:V] }]
      items&.each do |key_pattern, value_pattern|
        if (key_pattern in [:@label, label,]) && !value_pattern
          name = label.delete ':'
          scope[name] = value_type
          breakable.call
        end
        match_pattern value_type, value_pattern, scope if value_pattern
      end
      if splat in [:var_field, [:@ident, name,]]
        scope[name] = KatakataIrb::Types::InstanceType.new Hash, K: key_type, V: value_type
        breakable.call
      end
    in [:if_mod, cond, ifpattern]
      match_pattern target, ifpattern, scope
      simulate_evaluate cond, scope
      breakable.call
    in [:dyna_symbol,]
    in [:const_path_ref,]
    else
      KatakataIrb.log_puts "Unimplemented match pattern: #{pattern}"
    end
  end

  def evaluate_mrhs(sexp, scope)
    args, kwargs, = retrieve_method_args sexp
    values = args.filter_map do |t|
      if t.is_a? KatakataIrb::Types::Splat
        simulate_evaluate t.item, scope
        # TODO
        nil
      else
        simulate_evaluate t, scope
      end
    end
    unless kwargs.empty?
      kvs = kwargs.map do |t|
        case t
        in KatakataIrb::Types::Splat
          simulate_evaluate t.item, scope
          # TODO
          [KatakataIrb::Types::SYMBOL, KatakataIrb::Types::OBJECT]
        in [key, value]
          key_type = (key in [:@label,]) ? KatakataIrb::Types::SYMBOL : simulate_evaluate(key, scope)
          [key_type, simulate_evaluate(value, scope)]
        end
      end
      key_type = KatakataIrb::Types::UnionType[*kvs.map(&:first)]
      value_type = KatakataIrb::Types::UnionType[*kvs.map(&:last)]
      kw = KatakataIrb::Types::InstanceType.new(Hash, K: key_type, V: value_type)
    end
    [values, kw]
  end

  def sized_splat(value, method, size)
    array_elem, non_array = partition_to_array value, method
    values = [KatakataIrb::Types::UnionType[*array_elem, *non_array]]
    values += [array_elem] * (size - 1) if array_elem && size >= 1
    values
  end

  def partition_to_array(value, method)
    arrays, non_arrays = value.types.partition { _1.is_a?(KatakataIrb::Types::InstanceType) && _1.klass == Array }
    non_arrays.select! do |type|
      to_array_result = simulate_call type, method, [], nil, nil, name_match: false
      if to_array_result.is_a?(KatakataIrb::Types::InstanceType) && to_array_result.klass == Array
        arrays << to_array_result
        false
      else
        true
      end
    end
    array_elem = arrays.empty? ? nil : KatakataIrb::Types::UnionType[*arrays.map { _1.params[:Elem] || KatakataIrb::Types::OBJECT }]
    non_array = non_arrays.empty? ? nil : KatakataIrb::Types::UnionType[*non_arrays]
    [array_elem, non_array]
  end

  def evaluate_massign(sexp, values, scope)
    values = sized_splat values, :to_ary, sexp.size unless values.is_a? Array
    rest_index = sexp.find_index { _1 in [:rest_param, ]}
    if rest_index
      pre = rest_index ? sexp[0...rest_index] : sexp
      post = rest_index ? sexp[rest_index + 1..] : []
      sexp[rest_index] in [:rest_param, rest_field]
      rest_values = values[pre.size...values.size - post.size] || []
      rest_type = KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*rest_values]
      pairs = pre.zip(values.first(pre.size)) + [[rest_field, rest_type]] + post.zip(values.last(post.size))
    else
      pairs = sexp.zip values
    end
    pairs.each do |field, value|
      case field
      in [:@ident, name,]
        # block arg mlhs
        scope[name] = value || KatakataIrb::Types::OBJECT
      in [:var_field, [:@gvar | :@ivar | :@cvar | :@ident | :@const, name,]]
        # massign
        scope[name] = value || KatakataIrb::Types::OBJECT
      in [:mlhs, *mlhs]
        evaluate_massign mlhs, value || [], scope
      in [:field, receiver,]
        # (a=x).b, c = value
        simulate_evaluate receiver, scope
      in [:aref_field, *field]
        # (a=x)[i=y, j=z], b = value
        simulate_evaluate [:aref, *field], scope
      in nil
        # a, *, b = value
      end
    end
  end

  def kwargs_type(kwargs, scope)
    return if kwargs.empty?
    keys = []
    values = []
    kwargs.each do |kv|
      if kv.is_a? KatakataIrb::Types::Splat
        hash = simulate_evaluate kv.item, scope
        unless hash.is_a?(KatakataIrb::Types::InstanceType) && hash.klass == Hash
          hash = simulate_call hash, :to_hash, [], nil, nil
        end
        if hash.is_a?(KatakataIrb::Types::InstanceType) && hash.klass == Hash
          keys << hash.params[:K] if hash.params[:K]
          values << hash.params[:V] if hash.params[:V]
        end
      else
        key, value = kv
        keys << ((key in [:@label,]) ? KatakataIrb::Types::SYMBOL : simulate_evaluate(key, scope))
        values << simulate_evaluate(value, scope)
      end
    end
    KatakataIrb::Types::InstanceType.new(Hash, K: KatakataIrb::Types::UnionType[*keys], V: KatakataIrb::Types::UnionType[*values])
  end

  def retrieve_method_call(sexp)
    optional = -> { _1 in [:@op, '&.',] }
    case sexp
    in [:fcall | :vcall, [:@ident | :@const | :@kw | :@op, method,]] # hoge
      [nil, method, [], [], nil, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | [:@op, '::',] | :'::' => dot, :call]
      [receiver, :call, [], [], nil, optional[dot]]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | [:@op, '::',] | :'::' => dot, method]
      method => [:@ident | :@const | :@kw | :@op, method,] unless method == :call
      [receiver, method, [], [], nil, optional[dot]]
    in [:command, [:@ident | :@const | :@kw | :@op, method,], args] # hoge 1, 2
      args, kwargs, block = retrieve_method_args args
      [nil, method, args, kwargs, block, false]
    in [:command_call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, [:@ident | :@const | :@kw | :@op, method,], args] # a.hoge 1; a.hoge 1, 2;
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block, optional[dot]]
    in [:method_add_arg, call, args]
      receiver, method, _arg, _kwarg, _block, opt = retrieve_method_call call
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block, opt]
    in [:method_add_block, call, block]
      receiver, method, args, kwargs, opt = retrieve_method_call call
      [receiver, method, args, kwargs, block, opt]
    end
  end

  def retrieve_method_args(sexp)
    case sexp
    in [:mrhs_add_star, args, star]
      args, = retrieve_method_args args
      [[*args, KatakataIrb::Types::Splat.new(star)], [], nil]
    in [:mrhs_new_from_args, [:args_add_star,] => args]
      args, = retrieve_method_args args
      [args, [], nil]
    in [:mrhs_new_from_args, [:args_add_star,] => args, last_arg]
      args, = retrieve_method_args args
      [[*args, last_arg], [], nil]
    in [:mrhs_new_from_args, args, last_arg]
      [[*args, last_arg], [], nil]
    in [:mrhs_new_from_args, args]
      [args, [], nil]
    in [:args_add_block, [:args_add_star,] => args, block_arg]
      args, kwargs, = retrieve_method_args args
      block_arg = [:void_stmt] if block_arg.nil? # method(*splat, &)
      [args, kwargs, block_arg]
    in [:args_add_block, [*args, [:bare_assoc_hash,] => kw], block_arg]
      block_arg = [:void_stmt] if block_arg.nil? # method(**splat, &)
      _, kwargs = retrieve_method_args kw
      [args, kwargs, block_arg]
    in [:args_add_block, [*args], block_arg]
      block_arg = [:void_stmt] if block_arg.nil? # method(arg, &)
      [args, [], block_arg]
    in [:bare_assoc_hash, kws]
      kwargs = []
      kws.each do |kw|
        if kw in [:assoc_splat, value,]
          kwargs << KatakataIrb::Types::Splat.new(value) if value
        elsif kw in [:assoc_new, [:@label, label,] => key, nil]
          name = label.delete ':'
          kwargs << [key, [:__var_ref_or_call, [name =~ /\A[A-Z]/ ? :@const : :@ident, name, [0, 0]]]]
        elsif kw in [:assoc_new, key, value]
          kwargs << [key, value]
        end
      end
      [[], kwargs, nil]
    in [:args_add_star, *args, [:bare_assoc_hash,] => kwargs]
      args, = retrieve_method_args [:args_add_star, *args]
      _, kwargs = retrieve_method_args kwargs
      [args, kwargs, nil]
    in [:args_add_star, pre_args, star_arg, *post_args]
      pre_args, = retrieve_method_args pre_args if pre_args in [:args_add_star,]
      args = star_arg ? [*pre_args, KatakataIrb::Types::Splat.new(star_arg), *post_args] : pre_args + post_args
      [args, [], nil]
    in [:arg_paren, args]
      args ? retrieve_method_args(args) : [[], [], nil]
    in [[:command | :command_call, ] => command_arg] # method(a b, c), method(a.b c, d)
      [[command_arg], [], nil]
    else
      [[], [], nil]
    end
  end

  def simulate_call(receiver, method_name, args, kwargs, block, name_match: true)
    methods = KatakataIrb::Types.rbs_methods receiver, method_name.to_sym, args, kwargs, !!block
    block_called = false
    type_breaks = methods.map do |method, given_params, method_params|
      receiver_vars = (receiver in KatakataIrb::Types::InstanceType) ? receiver.params : {}
      free_vars = method.type.free_variables - receiver_vars.keys.to_set
      vars = receiver_vars.merge KatakataIrb::Types.match_free_variables(free_vars, method_params, given_params)
      if block && method.block
        params_type = method.block.type.required_positionals.map do |func_param|
          KatakataIrb::Types.from_rbs_type func_param.type, receiver, vars
        end
        self_type = KatakataIrb::Types.from_rbs_type method.block.self_type, receiver, vars if method.block.self_type
        block_response, breaks = block.call params_type, self_type
        block_called = true
        vars.merge! KatakataIrb::Types.match_free_variables(free_vars - vars.keys.to_set, [method.block.type.return_type], [block_response])
      end
      [KatakataIrb::Types.from_rbs_type(method.type.return_type, receiver, vars || {}), breaks]
    end
    block&.call [], nil unless block_called
    types = type_breaks.map(&:first)
    breaks = type_breaks.map(&:last).compact
    types << OBJECT_METHODS[method_name.to_sym] if name_match && OBJECT_METHODS.has_key?(method_name.to_sym)

    if method_name.to_sym == :new
      receiver.types.each do |type|
        if (type in KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
          types << KatakataIrb::Types::InstanceType.new(type.module_or_class)
        end
      end
    end
    KatakataIrb::Types::UnionType[*types, *breaks]
  end

  def extract_param_names(params)
    params => [:params, pre_required, optional, rest, post_required, keywords, keyrest, block]
    names = []
    extract_mlhs = ->(item) do
      case item
      in [:var_field, [:@ident, name,],]
        names << name
      in [:@ident, name,]
        names << name
      in [:mlhs, *items]
        items.each(&extract_mlhs)
      in [:rest_param, item]
        extract_mlhs.call item if item
      in [:field | :aref_field,]
        # a.b, c[i] = value
      in [:excessed_comma]
      in [:args_forward]
      end
    end
    [*pre_required, *post_required].each(&extract_mlhs)
    extract_mlhs.call rest if rest
    optional&.each do |key, _value|
      key => [:@ident, name,]
      names << name
    end
    keywords&.each do |key, _value|
      key => [:@label, label,]
      names << label.delete(':')
    end
    if keyrest in [:kwrest_params, [:@ident, name,]]
      names << name
    end
    if block in [:blockarg, [:@ident, name,]]
      names << name
    end
    names
  end

  def evaluate_assign_params(params, values, scope)
    values = values.dup
    params => [:params, pre_required, optional, rest, post_required, _keywords, keyrest, block]
    size = (pre_required&.size || 0) + (optional&.size || 0) + (post_required&.size || 0) + (rest ? 1 : 0)
    values = sized_splat values.first, :to_ary, size if values.size == 1 && size >= 2
    pre_values = values.shift pre_required.size if pre_required
    post_values = values.pop post_required.size if post_required
    opt_values = values.shift optional.size if optional
    rest_values = values
    evaluate_massign pre_required, pre_values, scope if pre_required
    evaluate_massign optional.map(&:first), opt_values, scope if optional
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*rest_values]
    end
    evaluate_massign post_required, post_values, scope if post_required
    # TODO: assign keywords
    if keyrest in [:kwrest_param, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::InstanceType.new Hash, K: KatakataIrb::Types::SYMBOL, V: KatakataIrb::Types::OBJECT
    end
    if block in [:blockarg, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::PROC
    end
  end

  def evaluate_param_defaults(params, scope)
    params => [:params, _pre_required, optional, rest, _post_required, keywords, keyrest, block]
    optional&.each do |item, value|
      item => [:@ident, name,]
      scope[name] = simulate_evaluate value, scope
    end
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::ARRAY
    end
    keywords&.each do |key, value|
      key => [:@label, label,]
      name = label.delete ':'
      scope[name] = value ? simulate_evaluate(value, scope) : KatakataIrb::Types::OBJECT
    end
    if keyrest in [:kwrest_param, [:@ident, name,]]
        scope[name] = KatakataIrb::Types::HASH
    end
    if block in [:blockarg, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::PROC
    end
  end

  def max_numbered_params(sexp)
    case sexp
    in [:do_block | :brace_block | :def | :class | :module,]
      0
    in [:var_ref, [:@ident, name,]]
      name.match?(/\A_[1-9]\z/) ? name[1..].to_i : 0
    else
      sexp.filter_map do |s|
        max_numbered_params s if s.is_a? Array
      end.max || 0
    end
  end

  def evaluate_program(program, scope)
    # statements.body[0] is local variable assign code
    program.statements.body[1..].each do |statement|
      simulate_evaluate statement, scope
    end
  end

  def self.calculate_binding_scope(binding, parents, target)
    dig_targets = DigTarget.new(parents, target) do |_types, scope|
      return scope
    end
    program = parents.first
    scope = KatakataIrb::Scope.from_binding(binding, program.locals)
    new(dig_targets).evaluate_program program, scope
    scope
  end

  def self.calculate_receiver(binding, parents, receiver)
    dig_targets = DigTarget.new([*parents, receiver], receiver) do |type, _scope|
      return type
    end
    program = parents.first
    new(dig_targets).evaluate_program program, KatakataIrb::Scope.from_binding(binding, program.locals)
    KatakataIrb::Types::NIL
  end
end
