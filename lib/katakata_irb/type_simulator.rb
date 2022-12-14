require_relative 'types'
require 'ripper'
require 'set'

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

  class BaseScope
    def initialize(binding, self_object)
      @binding, @self_object = binding, self_object
      @cache = { SELF => KatakataIrb::Types.type_from_object(self_object) }
      @local_variables = binding.local_variables.map(&:to_s).to_set
    end

    def mutable?() = false

    def [](name)
      @cache[name] ||= (
        fallback = KatakataIrb::Types::NIL
        case BaseScope.type_by_name name
        when :cvar
          KatakataIrb::TypeSimulator.type_of(fallback:) { @self_object.class_variable_get name }
        when :ivar
          KatakataIrb::TypeSimulator.type_of(fallback:) { @self_object.instance_variable_get name }
        when :lvar
          KatakataIrb::TypeSimulator.type_of(fallback:) { @binding.local_variable_get(name) }
        when :const
          KatakataIrb::TypeSimulator.type_of(fallback:) { @binding.eval name }
        end
      )
    end

    def self_type
      self[SELF]
    end

    def local_variables
      @local_variables.to_a
    end

    def self.type_by_name(name)
      if name.start_with? '@@'
        :cvar
      elsif name.start_with? '@'
        :ivar
      elsif name.start_with? '$'
        :gvar
      elsif name.start_with? '%'
        :internal
      elsif name[0].downcase != name[0]
        :const
      else
        :lvar
      end
    end

    def has?(name)
      case BaseScope.type_by_name name
      when :cvar
        @self_object.class_variable_defined? name
      when :ivar
        @self_object.instance_variable_defined? name
      when :lvar
        @local_variables.include? name
      when :const
        @binding.eval("#{name};true") rescue false
      when :internal
        true
      end
    end
  end

  class Scope
    attr_reader :parent, :jump_branches

    def self.from_binding(binding) = new BaseScope.new(binding, binding.eval('self'))

    def initialize(parent, table = {}, trace_cvar: true, trace_ivar: true, trace_lvar: true, passthrough: false)
      @tables = [table]
      @parent = parent
      @trace_cvar = trace_cvar
      @trace_ivar = trace_ivar
      @trace_lvar = trace_lvar
      @passthrough = passthrough
      @terminated = false
      @jump_branches = []
    end

    def mutable? = true

    def terminated?
      @terminated
    end

    def terminate_with(type, value)
      return if terminated?
      self[type] = value
      store_jump type
      terminate
    end

    def store_jump(type)
      scopes = ancestors.select(&:mutable?)
      scope = scopes.find { _1.has_own? type } || scopes.last
      index = scopes.index scope
      scope.jump_branches << scopes.drop(index).map(&:branch_table_clone)
    end

    def terminate
      @terminated = true
    end

    def branch_table_clone() = @tables.last.dup

    def trace?(name)
      return false unless @parent
      type = BaseScope.type_by_name(name)
      type == :cvar ? @trace_cvar : type == :ivar ? @trace_ivar : type == :lvar ? @trace_lvar : true
    end

    def [](name)
      @tables.reverse_each do |table|
        return table[name] if table.key? name
      end
      @parent[name] if trace? name
    end

    def []=(name, type)
      if @passthrough && BaseScope.type_by_name(name) != :internal
        @parent[name] = type
      elsif trace?(name) && @parent.mutable? && !@tables.any? { _1.key? name } && @parent.has?(name)
        @parent[name] = type
      else
        @tables.last[name] = type
      end
    end

    def self_type
      self[SELF]
    end

    def local_variables
      lvar_keys = @tables.flat_map(&:keys).select do |name|
        BaseScope.type_by_name(name) == :lvar
      end
      lvar_keys |= @parent.local_variables if @trace_lvar
      lvar_keys
    end

    def start_branch
      @tables << {}
    end

    def end_branch
      @tables.pop
    end

    def merge_jumps
      if terminated?
        merge @jump_branches
      else
        merge [*@jump_branches, [{}] * ancestors.size]
      end
    end

    def merge_branch(tables)
      target_table = @tables.last
      keys = tables.flat_map(&:keys).uniq
      keys.each do |key|
        original_value = self[key] || KatakataIrb::Types::NIL
        target_table[key] = KatakataIrb::Types::UnionType[*tables.map { _1[key] || original_value }.uniq]
      end
    end

    def ancestors
      scopes = [self]
      scopes << scopes.last.parent while scopes.last.parent&.mutable?
      scopes
    end

    def conditional(&block)
      run_branches(block, -> {}).first || KatakataIrb::Types::NIL
    end

    def never(&block)
      branch(&block)
    end

    def run_branches(*blocks)
      results = blocks.map { branch(&_1) }.reject(&:last)
      merge results.map { _2 }
      if results.empty?
        terminate
        []
      else
        results.map(&:first)
      end
    end

    def branch
      scopes = ancestors
      scopes.each(&:start_branch)
      @terminated = false
      result = yield
      terminated = @terminated
      @terminated = false
      [result, scopes.map(&:end_branch), terminated]
    end

    def merge(branches)
      scopes = ancestors
      scopes.zip(*branches).each do |scope, *tables|
        scope.merge_branch(tables)
      end
    end

    def base_scope
      @parent&.mutable? ? @parent.base_scope : @parent
    end

    def has_own?(name)
      @tables.any? { _1.key? name }
    end

    def has?(name)
      has_own?(name) || (trace?(name) && @parent.has?(name))
    end
  end

  module LexerElemMatcher
    refine Ripper::Lexer::Elem do
      def deconstruct_keys(_keys)
        {
          tok:,
          event:,
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

  SELF = '%self'
  BREAK_RESULT = '%break'
  NEXT_RESULT = '%next'
  RETURN_RESULT = '%return'
  PATTERNMATCH_BREAK = '%match'
  RAISE_BREAK = '%raise'

  def initialize(dig_targets)
    @dig_targets = dig_targets
  end

  def simulate_evaluate(sexp, scope, case_target: nil)
    result = simulate_evaluate_inner(sexp, scope, case_target:)
    @dig_targets.resolve result, scope if @dig_targets.target?(sexp)
    result
  end

  def simulate_evaluate_inner(sexp, scope, case_target: nil)
    case sexp
    in [:program, statements]
      statements.map { simulate_evaluate _1, scope }.last
    in [:def | :defs,]
      sexp in [:def, _method_name_exp, params, body_stmt]
      sexp in [:defs, receiver_exp, _dot_exp, _method_name_exp, params, body_stmt]
      if receiver_exp
        receiver_exp in [:paren, receiver_exp]
        self_type = simulate_evaluate receiver_exp, scope
      else
        current_self_types = scope.self_type.types
        self_types = current_self_types.map do |type|
          if (type in KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
            KatakataIrb::Types::InstanceType.new type.module_or_class
          else
            type
          end
        end
        self_type = KatakataIrb::Types::UnionType[*self_types]
      end
      if @dig_targets.dig? sexp
        params in [:paren, params]
        params_table = extract_param_names(params).to_h { [_1, KatakataIrb::Types::NIL] }
        method_scope = Scope.new scope, { **params_table, SELF => self_type, BREAK_RESULT => nil, NEXT_RESULT => nil, RETURN_RESULT => nil }, trace_lvar: false
        evaluate_assign_params params, [], method_scope
        method_scope.conditional { evaluate_param_defaults params, method_scope }
        simulate_evaluate body_stmt, method_scope
      end
      KatakataIrb::Types::SYMBOL
    in [:@int,]
      KatakataIrb::Types::INTEGER
    in [:@float,]
      KatakataIrb::Types::FLOAT
    in [:@rational,]
      KatakataIrb::Types::RATIONAL
    in [:@imaginary,]
      KatakataIrb::Types::COMPLEX
    in [:@tstring_content,]
      KatakataIrb::Types::STRING
    in [:symbol_literal,]
      KatakataIrb::Types::SYMBOL
    in [:dyna_symbol, [:string_content, *statements]]
      statements.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::SYMBOL
    in [:@CHAR,]
      KatakataIrb::Types::STRING
    in [:@backref,]
      KatakataIrb::Types::UnionType[KatakataIrb::Types::STRING, KatakataIrb::Types::NIL]
    in [:string_literal, [:string_content, *statements]]
      statements.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::STRING
    in [:xstring_literal, statements]
      statements.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::STRING
    in [:string_embexpr, statements]
      statements.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::STRING
    in [:string_dvar,]
      KatakataIrb::Types::STRING
    in [:regexp_literal, statements, _regexp_end]
      statements.each { simulate_evaluate _1, scope }
      KatakataIrb::Types::REGEXP
    in [:array, [:args_add_star,] => star]
      args, kwargs = retrieve_method_args star
      types = args.flat_map do |elem|
        if elem in KatakataIrb::Types::Splat
          splat = simulate_evaluate elem.item, scope
          array_value = to_array splat, :to_a
          array_value ? (array_value.params[:Elem] || []) : splat
        else
          simulate_evaluate elem, scope
        end
      end
      types << kwargs_type(kwargs, scope) if kwargs && kwargs.any?
      KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*types]
    in [:array, statements]
      if statements.nil? || statements.empty?
        KatakataIrb::Types::ARRAY
      elsif statements.all? { _1 in [Symbol,] }
        # normal array
        elem = statements ? KatakataIrb::Types::UnionType[*statements.map { simulate_evaluate _1, scope }] : KatakataIrb::Types::NIL
        KatakataIrb::Types::InstanceType.new Array, Elem: elem
      else
        # %I[] or %W[]
        statements.each do |sub_statements|
          sub_statements.each { simulate_evaluate _1, scope }
        end
        # TODO: use AST because Ripper.sexp('%I[a]') == Ripper.sexp('%W[a]')
        elem = KatakataIrb::Types::UnionType[KatakataIrb::Types::STRING, KatakataIrb::Types::SYMBOL]
        KatakataIrb::Types::InstanceType.new Array, Elem: elem
      end
    in [:bare_assoc_hash, args]
      simulate_evaluate [:hash, [:assoclist_from_args, args]], scope
    in [:hash, [:assoclist_from_args, args]]
      keys = []
      values = []
      args.each do |arg|
        case arg
        in [:assoc_new, key, value]
          if key in [:@label, label, pos]
            keys << KatakataIrb::Types::SYMBOL
            name = label.delete ':'
            value ||= [:__var_ref_or_call, [name =~ /\A[A-Z]/ ? :@const : :@ident, name, pos]]
          else
            keys << simulate_evaluate(key, scope)
          end
          values << simulate_evaluate(value, scope)
        in [:assoc_splat, value]
          hash = simulate_evaluate value, scope
          unless (hash in KatakataIrb::Types::InstanceType) && hash.klass == Hash
            hash = simulate_call hash, :to_hash, [], nil, nil
          end
          if (hash in KatakataIrb::Types::InstanceType) && hash.klass == Hash
            keys << hash.params[:K] if hash.params[:K]
            values << hash.params[:V] if hash.params[:V]
          end
        end
      end
      KatakataIrb::Types::InstanceType.new Hash, K: KatakataIrb::Types::UnionType[*keys], V: KatakataIrb::Types::UnionType[*values]
    in [:hash, nil]
      KatakataIrb::Types::InstanceType.new Hash
    in [:paren, [Symbol,] | false => statement]
      # workaround for `p ()` and `p (foo)`
      simulate_evaluate statement, scope if statement
    in [:paren | :ensure | :else, statements]
      statements.map { simulate_evaluate _1, scope }.last
    in [:const_path_ref, receiver, [:@const, name,]]
      r = simulate_evaluate receiver, scope
      (r in KatakataIrb::Types::SingletonType) ? self.class.type_of { r.module_or_class.const_get name } : KatakataIrb::Types::NIL
    in [:__var_ref_or_call, [type, name, pos]]
      sexp = scope.has?(name) ? [:var_ref, [type, name, pos]] : [:vcall, [:@ident, name, pos]]
      simulate_evaluate sexp, scope
    in [:var_ref, [:@kw, name,]]
      case name
      in 'self'
        scope.self_type
      in 'true'
        KatakataIrb::Types::TRUE
      in 'false'
        KatakataIrb::Types::FALSE
      in 'nil'
        KatakataIrb::Types::NIL
      in '__FILE__'
        KatakataIrb::Types::STRING
      in '__LINE__'
        KatakataIrb::Types::INTEGER
      in '__ENCODING__'
        KatakataIrb::Types::InstanceType.new Encoding
      end
    in [:var_ref, [:@const | :@ivar | :@cvar | :@gvar | :@ident, name,]]
      scope[name] || KatakataIrb::Types::NIL
    in [:const_ref, [:@const, name,]]
      scope[name] || KatakataIrb::Types::NIL
    in [:aref, receiver, args]
      receiver_type = simulate_evaluate receiver, scope if receiver
      args, kwargs, _block = retrieve_method_args args
      args_type = args.map do |arg|
        if arg in KatakataIrb::Types::Splat
          simulate_evaluate arg.item, scope
          nil # TODO: splat
        else
          simulate_evaluate arg, scope
        end
      end
      simulate_call receiver_type, :[], args_type, kwargs_type(kwargs, scope), nil
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      if (sexp in [:vcall, [:@ident, name,]]) && scope.has?(name)
        # workaround for https://bugs.ruby-lang.org/issues/19175
        return scope[name]
      end
      receiver, method, args, kwargs, block, conditional = retrieve_method_call sexp
      if receiver.nil? && method == 'raise'
        scope.terminate_with RAISE_BREAK, KatakataIrb::Types::TRUE
        return KatakataIrb::Types::NIL
      end
      receiver_type = receiver ? simulate_evaluate(receiver, scope) : scope.self_type
      evaluate_method = lambda do
        args_type = args.map do |arg|
          if arg in KatakataIrb::Types::Splat
            simulate_evaluate arg.item, scope
            nil # TODO: splat
          else
            simulate_evaluate arg, scope
          end
        end

        if block
          if block in [:symbol_literal, [:symbol, [:@ident, block_name,]]]
            call_block_proc = ->(block_args) do
              block_receiver, *rest = block_args
              block_receiver ? simulate_call(block_receiver || KatakataIrb::Types::OBJECT, block_name, rest, nil, nil) : KatakataIrb::Types::OBJECT
            end
          elsif block in [:do_block | :brace_block => type, block_var, body]
            block_var in [:block_var, params,]
            call_block_proc = ->(block_args) do
              result, breaks, nexts = scope.conditional do
                if params
                  names = extract_param_names(params)
                else
                  names = (1..max_numbered_params(body)).map { "_#{_1}" }
                  params = [:params, names.map { [:@ident, _1, [0, 0]] }, nil, nil, nil, nil, nil, nil]
                end
                params_table = names.zip(block_args).to_h { [_1, _2 || KatakataIrb::Types::NIL] }
                block_scope = Scope.new scope, { **params_table, BREAK_RESULT => nil, NEXT_RESULT => nil }
                evaluate_assign_params params, block_args, block_scope
                block_scope.conditional { evaluate_param_defaults params, block_scope } if params
                if type == :do_block
                  result = simulate_evaluate body, block_scope
                else
                  result = body.map { simulate_evaluate _1, block_scope }.last
                end
                block_scope.merge_jumps
                result = KatakataIrb::Types::NIL if block_scope.terminated?
                [result, block_scope[BREAK_RESULT], block_scope[NEXT_RESULT]]
              end
              [KatakataIrb::Types::UnionType[result, *nexts], breaks]
            end
          else
            call_block_proc = ->(_block_args) { KatakataIrb::Types::OBJECT }
            simulate_evaluate block, scope
          end
        end
        simulate_call receiver_type, method, args_type, kwargs_type(kwargs, scope), call_block_proc
      end
      if conditional
        scope.conditional { evaluate_method.call }
      else
        evaluate_method.call
      end
    in [:binary, a, Symbol => op, b]
      atype = simulate_evaluate a, scope
      case op
      when :'&&', :and
        btype = scope.conditional { simulate_evaluate b, scope }
        KatakataIrb::Types::UnionType[btype, KatakataIrb::Types::NIL, KatakataIrb::Types::FALSE]
      when :'||', :or
        btype = scope.conditional { simulate_evaluate b, scope }
        KatakataIrb::Types::UnionType[atype, btype]
      else
        btype = simulate_evaluate b, scope
        simulate_call atype, op, [btype], nil, nil
      end
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, scope), op, [], nil, nil
    in [:lambda, params, statements]
      params in [:paren, params] # ->{}, -> do end
      statements in [:bodystmt, statements, _unknown, _unknown, _unknown] # -> do end
      params in [:paren, params]
      params_table = extract_param_names(params).to_h { [_1, KatakataIrb::Types::NIL] }
      block_scope = Scope.new scope, { **params_table, BREAK_RESULT => nil, NEXT_RESULT => nil, RETURN_RESULT => nil }
      evaluate_assign_params params, [], block_scope
      block_scope.conditional { evaluate_param_defaults params, block_scope }
      statements.each { simulate_evaluate _1, block_scope }
      block_scope.merge_jumps
      KatakataIrb::Types::ProcType.new
    in [:assign, [:var_field, [:@gvar | :@ivar | :@cvar | :@ident | :@const, name,]], value]
      res = simulate_evaluate value, scope
      scope[name] = res
      res
    in [:assign, [:aref_field, receiver, key], value]
      simulate_evaluate receiver, scope
      args, kwargs, _block = retrieve_method_args key
      args.each do |arg|
        item = ((arg in KatakataIrb::Types::Splat) ? arg.item : arg)
        simulate_evaluate item, scope
      end
      kwargs_type kwargs, scope
      simulate_evaluate value, scope
    in [:assign, [:field, receiver, period, [:@ident,]], value]
      simulate_evaluate receiver, scope
      if period in [:@op, '&.',]
        scope.conditional { simulate_evaluate value, scope }
      else
        simulate_evaluate value, scope
      end
    in [:opassign, target, [:@op, op,], value]
      op = op.to_s.delete('=').to_sym
      if target in [:var_field, *field]
        receiver = [:var_ref, *field]
      elsif target in [:field, *field]
        receiver = [:call, *field]
      elsif target in [:aref_field, *field]
        receiver = [:aref, *field]
      else
        receiver = target
      end
      simulate_evaluate [:assign, target, [:binary, receiver, op, value]], scope
    in [:assign, target, value]
      simulate_evaluate target, scope
      simulate_evaluate value, scope
    in [:massign, targets, value]
      targets in [:mlhs, *targets] # (a,b) = value
      rhs = simulate_evaluate value, scope
      evaluate_massign targets, rhs, scope
      rhs
    in [:mrhs_new_from_args | :mrhs_add_star,]
      values, = evaluate_mrhs sexp, scope
      KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*values]
    in [:ifop, cond, tval, fval]
      simulate_evaluate cond, scope
      KatakataIrb::Types::UnionType[*scope.run_branches(
        -> { simulate_evaluate tval, scope },
        -> { simulate_evaluate fval, scope }
      )]
    in [:if_mod | :unless_mod, cond, statement]
      simulate_evaluate cond, scope
      KatakataIrb::Types::UnionType[scope.conditional { simulate_evaluate statement, scope }, KatakataIrb::Types::NIL]
    in [:if | :unless | :elsif, cond, statements, else_statement]
      simulate_evaluate cond, scope
      results = scope.run_branches(
        -> { statements.map { simulate_evaluate _1, scope }.last },
        -> { else_statement ? simulate_evaluate(else_statement, scope) : KatakataIrb::Types::NIL }
      )
      results.empty? ? KatakataIrb::Types::NIL : KatakataIrb::Types::UnionType[*results]
    in [:while | :until, cond, statements]
      inner_scope = Scope.new scope, { BREAK_RESULT => nil }, passthrough: true
      simulate_evaluate cond, inner_scope
      scope.conditional { statements.each { simulate_evaluate _1, inner_scope } }
      inner_scope.merge_jumps
      breaks = inner_scope[BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, KatakataIrb::Types::NIL] : KatakataIrb::Types::NIL
    in [:while_mod | :until_mod, cond, statement]
      inner_scope = Scope.new scope, { BREAK_RESULT => nil }, passthrough: true
      simulate_evaluate cond, inner_scope
      scope.conditional { simulate_evaluate statement, inner_scope }
      inner_scope.merge_jumps
      breaks = inner_scope[BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, KatakataIrb::Types::NIL] : KatakataIrb::Types::NIL
    in [:break | :next | :return => jump_type, value]
      internal_key = jump_type == :break ? BREAK_RESULT : jump_type == :next ? NEXT_RESULT : RETURN_RESULT
      if value.empty?
        jump_value = KatakataIrb::Types::NIL
      else
        values, kw = evaluate_mrhs value, scope
        values << kw if kw
        jump_value = values.size == 1 ? values.first : KatakataIrb::Types::InstanceType.new(Array, Elem: KatakataIrb::Types::UnionType[*values])
      end
      scope.terminate_with internal_key, jump_value
      KatakataIrb::Types::NIL
    in [:return0]
      scope.terminate_with RETURN_RESULT, KatakataIrb::Types::NIL
      KatakataIrb::Types::NIL
    in [:yield, args]
      evaluate_mrhs args, scope
      KatakataIrb::Types::OBJECT
    in [:yield0]
      KatakataIrb::Types::OBJECT
    in [:redo | :retry]
      scope.terminate
    in [:super, args]
      args, kwargs, _block = retrieve_method_args args
      args.each do |arg|
        item = ((arg in KatakataIrb::Types::Splat) ? arg.item : arg)
        simulate_evaluate item, scope
      end
      kwargs_type kwargs, scope
      KatakataIrb::Types::OBJECT
    in [:begin, body_stmt]
      simulate_evaluate body_stmt, scope
    in [:bodystmt, statements, rescue_stmt, _unknown, ensure_stmt]
      statements = [statements] if statements in [Symbol,] # oneliner-def body
      rescue_scope = Scope.new scope, { RAISE_BREAK => nil }, passthrough: true if rescue_stmt
      return_type = statements.map { simulate_evaluate _1, rescue_scope || scope }.last
      rescue_scope&.merge_jumps
      if rescue_stmt
        return_type = KatakataIrb::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_stmt, scope }]
      end
      simulate_evaluate ensure_stmt, scope if ensure_stmt
      return_type
    in [:rescue, error_class_stmts, error_var_stmt, statements, rescue_stmt]
      return_type = scope.conditional do
        if error_var_stmt in [:var_field, [:@ident, error_var,]]
          if (error_class_stmts in [:mrhs_new_from_args, Array => stmts, stmt])
            error_class_stmts = [*stmts, stmt]
          end
          error_classes = (error_class_stmts || []).flat_map { simulate_evaluate _1, scope }.uniq
          error_types = error_classes.filter_map { KatakataIrb::Types::InstanceType.new _1.module_or_class if _1 in KatakataIrb::Types::SingletonType }
          error_types << KatakataIrb::Types::InstanceType.new(StandardError) if error_types.empty?
          scope[error_var] = KatakataIrb::Types::UnionType[*error_types]
        end
        statements.map { simulate_evaluate _1, scope }.last
      end
      if rescue_stmt
        return_type = KatakataIrb::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_stmt, scope }]
      end
      return_type
    in [:rescue_mod, statement1, statement2]
      rescue_scope = Scope.new scope, { RAISE_BREAK => nil }, passthrough: true
      a = simulate_evaluate statement1, rescue_scope
      rescue_scope.merge_jumps
      b = scope.conditional { simulate_evaluate statement2, scope }
      KatakataIrb::Types::UnionType[a, b]
    in [:module, module_stmt, body_stmt]
      module_types = simulate_evaluate(module_stmt, scope).types.grep(KatakataIrb::Types::SingletonType)
      module_types << KatakataIrb::Types::MODULE if module_types.empty?
      simulate_evaluate body_stmt, Scope.new(scope, { SELF => KatakataIrb::Types::UnionType[*module_types], BREAK_RESULT => nil, NEXT_RESULT => nil, RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
    in [:sclass, klass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope).types.filter_map do |type|
        KatakataIrb::Types::SingletonType.new type.klass if type in KatakataIrb::Types::InstanceType
      end
      klass_types = [KatakataIrb::Types::CLASS] if klass_types.empty?
      simulate_evaluate body_stmt, Scope.new(scope, { SELF => KatakataIrb::Types::UnionType[*klass_types], BREAK_RESULT => nil, NEXT_RESULT => nil, RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
    in [:class, klass_stmt, superclass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope).types
      klass_types += simulate_evaluate(superclass_stmt, scope).types if superclass_stmt
      klass_types = klass_types.select do |type|
        (type in KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
      end
      klass_types << KatakataIrb::Types::CLASS if klass_types.empty?
      simulate_evaluate body_stmt, Scope.new(scope, { SELF => KatakataIrb::Types::UnionType[*klass_types], BREAK_RESULT => nil, NEXT_RESULT => nil, RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
    in [:for, fields, enum, statements]
      fields = [fields] if fields in [:var_field | :field | :aref_field,]
      params = [:params, fields, nil, nil, nil, nil, nil, nil]
      enum = simulate_evaluate enum, scope
      extract_param_names(params).each { scope[_1] = KatakataIrb::Types::NIL }
      response = simulate_call enum, :first, [], nil, nil
      evaluate_assign_params params, [response], scope
      inner_scope = Scope.new scope, { BREAK_RESULT => nil }, passthrough: true
      scope.conditional do
        statements.each { simulate_evaluate _1, inner_scope }
      end
      inner_scope.merge_jumps
      breaks = inner_scope[BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, enum] : enum
    in [:when, pattern, if_statements, else_statement]
      eval_pattern = lambda do |pattern, *rest|
        simulate_evaluate pattern, scope
        scope.conditional { eval_pattern.call(*rest) } if rest.any?
      end
      if_branch = lambda do
        eval_pattern.call(*pattern)
        if_statements.map { simulate_evaluate _1, scope }.last
      end
      else_branch = lambda do
        pattern.each { simulate_evaluate _1, scope }
        simulate_evaluate(else_statement, scope, case_target:)
      end
      if if_statements && else_statement
        KatakataIrb::Types::UnionType[*scope.run_branches(if_branch, else_branch)]
      else
        KatakataIrb::Types::UnionType[scope.conditional { (if_branch || else_branch).call }, KatakataIrb::Types::NIL]
      end
    in [:in, [:var_field, [:@ident, name,]], if_statements, else_statement]
      scope.never { simulate_evaluate else_statement, scope } if else_statement
      scope[name] = case_target || KatakataIrb::Types::OBJECT
      if_statements ? if_statements.map { simulate_evaluate _1, scope }.last : KatakataIrb::Types::NIL
    in [:in, pattern, if_statements, else_statement]
      pattern_scope = Scope.new(scope, { PATTERNMATCH_BREAK => nil }, passthrough: true)
      results = scope.run_branches(
        -> {
          match_pattern case_target, pattern, pattern_scope
          if_statements ? if_statements.map { simulate_evaluate _1, scope }.last : KatakataIrb::Types::NIL
        },
        -> {
          pattern_scope.merge_jumps
          else_statement ? simulate_evaluate(else_statement, scope, case_target:) : KatakataIrb::Types::NIL
        }
      )
      KatakataIrb::Types::UnionType[*results]
    in [:case, target_exp, match_exp]
      target = simulate_evaluate target_exp, scope
      simulate_evaluate match_exp, scope, case_target: target
    in [:void_stmt]
      KatakataIrb::Types::NIL
    in [:dot2 | :dot3, range_beg, range_end]
      simulate_evaluate range_beg, scope if range_beg
      simulate_evaluate range_end, scope if range_end
      KatakataIrb::Types::RANGE
    in [:top_const_ref, [:@const, name,]]
      self.class.type_of { Object.const_get name }
    else
      KatakataIrb.log_puts
      KatakataIrb.log_puts :NOMATCH
      KatakataIrb.log_puts sexp.inspect
      KatakataIrb::Types::NIL
    end
  end

  def match_pattern(target, pattern, scope)
    breakable = -> { scope.store_jump PATTERNMATCH_BREAK }
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
      scope.conditional { match_pattern target, rpattern, scope }
      breakable.call
    in [:binary, lpattern, :'=>', [:var_field, [:@ident, name,]] => rpattern]
      if lpattern in [:var_ref, [:@const, _const_name,]]
        const_value = simulate_evaluate lpattern, scope
        if (const_value in KatakataIrb::Types::SingletonType) && const_value.module_or_class.is_a?(Class)
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
      array_types = types.select { (_1 in KatakataIrb::Types::InstanceType) && _1.klass == Array }
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
      hash_types = types.select { (_1 in KatakataIrb::Types::InstanceType) && _1.klass == Hash }
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
      if t in KatakataIrb::Types::Splat
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

  def to_array(value, method)
    return value if (value in KatakataIrb::Types::InstanceType) && value.klass == Array
    to_array_result = simulate_call value, method, [], nil, nil, name_match: false
    return to_array_result if (to_array_result in KatakataIrb::Types::InstanceType) && to_array_result.klass == Array
  end

  def evaluate_massign(sexp, values, scope)
    unless values in Array
      array_value = to_array values, :to_ary
      values = array_value ? [array_value.params[:Elem] || KatakataIrb::Types::OBJECT] * sexp.size : [values]
    end

    rest_index = sexp.find_index { _1 in [:rest_param, ]}
    if rest_index
      pre = rest_index ? sexp[0...rest_index] : sexp
      post = rest_index ? sexp[rest_index + 1..] : []
      sexp[rest_index] in [:rest_param, rest_field]
      rest_values = values[pre.size...-post.size] || []
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
      in [:var_field, [:@ident | :@ivar | :@cvar | :@gvar, name,]]
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
      if kv in KatakataIrb::Types::Splat
        hash = simulate_evaluate kv.item, scope
        unless (hash in KatakataIrb::Types::InstanceType) && hash.klass == Hash
          hash = simulate_call hash, :to_hash, [], nil, nil
        end
        if (hash in KatakataIrb::Types::InstanceType) && hash.klass == Hash
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

  def self.type_of(fallback: KatakataIrb::Types::OBJECT)
    begin
      KatakataIrb::Types.type_from_object yield
    rescue
      fallback
    end
  end

  def retrieve_method_call(sexp)
    conditional = -> { _1 in [:@op, '&.',] }
    case sexp
    in [:fcall | :vcall, [:@ident | :@const | :@kw | :@op, method,]] # hoge
      [nil, method, [], [], nil, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, :call]
      [receiver, :call, [], [], nil, conditional[dot]]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, method]
      method => [:@ident | :@const | :@kw | :@op, method,] unless method == :call
      [receiver, method, [], [], nil, conditional[dot]]
    in [:command, [:@ident | :@const | :@kw | :@op, method,], args] # hoge 1, 2
      args, kwargs, block = retrieve_method_args args
      [nil, method, args, kwargs, block, false]
    in [:command_call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, [:@ident | :@const | :@kw | :@op, method,], args] # a.hoge 1; a.hoge 1, 2;
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block, conditional[dot]]
    in [:method_add_arg, call, args]
      receiver, method, _arg, _kwarg, _block, cond = retrieve_method_call call
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block, cond]
    in [:method_add_block, call, block]
      receiver, method, args, kwargs, cond = retrieve_method_call call
      [receiver, method, args, kwargs, block, cond]
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
        block_response, breaks = block.call params_type
        block_called = true
        vars.merge! KatakataIrb::Types.match_free_variables(free_vars - vars.keys.to_set, [method.block.type.return_type], [block_response])
      end
      [KatakataIrb::Types.from_rbs_type(method.type.return_type, receiver, vars || {}), breaks]
    end
    block&.call [] unless block_called
    types = type_breaks.map(&:first)
    breaks = type_breaks.map(&:last).compact
    types << OBJECT_METHODS[method_name.to_sym] if name_match && OBJECT_METHODS.has_key?(method_name.to_sym)
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
    if values.size == 1 && size >= 2
      value = values.first
      array_value = to_array value, :to_ary if value
      values = [array_value.params[:Elem] || KatakataIrb::Types::OBJECT] * size if array_value
    end
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
        max_numbered_params s if s in Array
      end.max || 0
    end
  end

  def self.calculate_binding_scope(binding, parents, target)
    dig_targets = DigTarget.new(parents, target) do |_types, scope|
      return scope
    end
    scope = Scope.from_binding(binding)
    new(dig_targets).simulate_evaluate parents[0], scope
    scope
  end

  def self.calculate_receiver(binding, parents, receiver)
    dig_targets = DigTarget.new(parents, receiver) do |type, _scope|
      return type
    end
    new(dig_targets).simulate_evaluate parents[0], Scope.from_binding(binding)
    KatakataIrb::Types::NIL
  end
end
