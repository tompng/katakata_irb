require_relative 'types'
require 'ripper'
require 'set'

module Completion; end
class Completion::TypeSimulator
  class JumpPoints
    def initialize
      @returns = []
      @breaks = []
      @nexts = []
    end
    def return(value) = @returns.last&.<< value
    def break(value) = @breaks.last&.<< value
    def next(value) = @nexts.last&.<< value

    def with(*types)
      accumulators = types.map do |type|
        ac = []
        case type
        in :return
          @returns << ac
        in :break
          @breaks << ac
        in :next
          @nexts << ac
        end
        ac
      end
      result = yield
      [result, *accumulators.map { Completion::Types::UnionType[*_1] }]
    ensure
      types.each do |type|
        case type
        in :return
          @returns.pop
        in :break
          @breaks.pop
        in :next
          @nexts.pop
        end
      end
    end
  end

  class DigTarget
    def initialize(parents, receiver, &block)
      @dig_ids = parents.to_h { [_1.__id__, true ] }
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
      @cache = { SELF => Completion::Types.type_from_object(self_object) }
      @local_variables = binding.local_variables.map(&:to_s).to_set
    end

    def mutable?() = false

    def [](name)
      @cache[name] ||= (
        fallback = Completion::Types::NIL
        case BaseScope.type_by_name name
        when :cvar
          Completion::TypeSimulator.type_of(fallback:) { @self_object.class_variable_get name }
        when :ivar
          Completion::TypeSimulator.type_of(fallback:) { @self_object.instance_variable_get name }
        when :lvar
          Completion::TypeSimulator.type_of(fallback:) { @binding.local_variable_get(name) }
        when :const
          Completion::TypeSimulator.type_of(fallback:) { @binding.eval name }
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
      elsif name[0].downcase != name[0]
        :const
      else
        name == SELF ? :self : :lvar
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
      when :self
        true
      end
    end
  end

  class Scope
    attr_reader :parent

    def self.from_binding(binding) = new BaseScope.new(binding, binding.eval('self'))

    def initialize(parent, table = {}, trace_cvar: true, trace_ivar: true, trace_lvar: true)
      @tables = [table]
      @parent = parent
      @trace_cvar = trace_cvar
      @trace_ivar = trace_ivar
      @trace_lvar = trace_lvar
    end

    def mutable?() = true

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
      raise if type.nil?
      if trace?(name) && @parent.mutable? && !@tables.any? { _1.key? name } && @parent.has?(name)
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
      lvar_keys | @parent.local_variables
    end

    def start_branch
      @tables << {}
    end

    def end_branch
      @tables.pop
    end

    def merge_branch(tables)
      target_table = @tables.last
      keys = tables.flat_map(&:keys).uniq
      keys.each do |key|
        original_value = self[key]
        target_table[key] = Completion::Types::UnionType[*tables.map { _1[key] || original_value }.uniq]
      end
    end

    def ancestors
      scopes = [self]
      while scopes.last.parent&.mutable?
        scopes << scopes.last.parent
      end
      scopes
    end

    def conditional(&block)
      run_branches(block, ->{}).first
    end

    def run_branches(*blocks)
      results = blocks.map { branch(&_1) }
      merge results.map(&:last)
      results.map(&:first)
    end

    def branch
      scopes = ancestors
      scopes.each(&:start_branch)
      result = yield
      [result, scopes.map(&:end_branch)]
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

    def has?(name)
      @tables.any? { _1.key? name } || (trace?(name) && @parent.has?(name))
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
    to_s: Completion::Types::STRING,
    to_str: Completion::Types::STRING,
    to_a: Completion::Types::ARRAY,
    to_ary: Completion::Types::ARRAY,
    to_h: Completion::Types::HASH,
    to_hash: Completion::Types::HASH,
    to_i: Completion::Types::INTEGER,
    to_int: Completion::Types::INTEGER,
    to_f: Completion::Types::FLOAT,
    to_c: Completion::Types::COMPLEX,
    to_r: Completion::Types::RATIONAL
  }

  SELF = '%self'
  def initialize(dig_targets)
    @dig_targets = dig_targets
    @jumps = JumpPoints.new
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
      sexp in [:def, method_name_exp, params, body_stmt]
      sexp in [:defs, receiver_exp, dot_exp, method_name_exp, params, body_stmt]
      if receiver_exp
        receiver_exp in  [:paren, receiver_exp]
        self_type = simulate_evaluate receiver_exp, scope
      else
        current_self_types = scope.self_type.types
        self_types = current_self_types.map do |type|
          if (type in Completion::Types::SingletonType) && type.module_or_class.is_a?(Class)
            Completion::Types::InstanceType.new type.module_or_class
          else
            type
          end
        end
        self_type = Completion::Types::UnionType[*self_types]
      end
      if @dig_targets.dig? sexp
        params in [:paren, params]
        params_table = extract_param_names(params).to_h { [_1, Completion::Types::NIL] }
        method_scope = Scope.new scope, { **params_table, SELF => self_type }, trace_lvar: false
        evaluate_assign_params params, [], method_scope
        method_scope.conditional { evaluate_param_defaults params, method_scope }
        simulate_evaluate body_stmt, method_scope
      end
      Completion::Types::SYMBOL
    in [:@int,]
      Completion::Types::INTEGER
    in [:@float,]
      Completion::Types::FLOAT
    in [:@rational,]
      Completion::Types::RATIONAL
    in [:@imaginary,]
      Completion::Types::COMPLEX
    in [:@tstring_content,]
      Completion::Types::STRING
    in [:symbol_literal,]
      Completion::Types::SYMBOL
    in [:dyna_symbol, [:string_content, *statements]]
      statements.each { simulate_evaluate _1, scope }
      Completion::Types::SYMBOL
    in [:@CHAR, ]
      Completion::Types::STRING
    in [:string_literal, [:string_content, *statements]]
      statements.each { simulate_evaluate _1, scope }
      Completion::Types::STRING
    in [:xstring_literal, statements]
      statements.each { simulate_evaluate _1, scope }
      Completion::Types::STRING
    in [:string_embexpr, statements]
      statements.each { simulate_evaluate _1, scope }
      Completion::Types::STRING
    in [:regexp_literal,]
      statements.each { simulate_evaluate _1, scope }
      Completion::Types::REGEXP
    in [:array, [:args_add_star,] => star]
      args, kwargs = retrieve_method_args star
      types = args.flat_map do |elem|
        if elem in Completion::Types::Splat
          splat = simulate_evaluate elem.item, scope
          unless (splat in Completion::Types::InstanceType) && splat.klass == Array
            to_a_result = simulate_call splat, :to_a, [], nil, nil, name_match: false
            splat = to_a_result if (to_a_result in Completion::Types::InstanceType) && splat.klass == Array
          end
          if (splat in Completion::Types::InstanceType) && splat.klass == Array
            splat.params[:Elem] || []
          else
            splat
          end
        else
          simulate_evaluate elem, scope
        end
      end
      types << kwargs_type(kwargs, scope) if kwargs && kwargs.any?
      Completion::Types::InstanceType.new Array, Elem: Completion::Types::UnionType[*types]
    in [:array, statements]
      elem = statements ? Completion::Types::UnionType[*statements.map { simulate_evaluate _1, scope }] : Completion::Types::NIL
      Completion::Types::InstanceType.new Array, Elem: elem
    in [:bare_assoc_hash, args]
      simulate_evaluate [:hash, [:assoclist_from_args, args]], scope
    in [:hash, [:assoclist_from_args, args]]
      keys = []
      values = []
      args.each do |arg|
        case arg
        in [:assoc_new, key, value]
          if key in [:@label, label, pos]
            keys << Completion::Types::SYMBOL
            name = label.delete ':'
            value ||= [:__var_ref_or_call, [name =~ /\A[A-Z]/ ? :@const : :@ident, name, pos]]
          else
            keys << simulate_evaluate(key, scope)
          end
          values << simulate_evaluate(value, scope)
        in [:assoc_splat, value]
          hash = simulate_evaluate value, scope
          unless (hash in Completion::Types::InstanceType) && hash.klass == Hash
            hash = simulate_call hash, :to_hash, [], nil, nil
          end
          if (hash in Completion::Types::InstanceType) && hash.klass == Hash
            keys << hash.params[:K] if hash.params[:K]
            values << hash.params[:V] if hash.params[:V]
          end
        end
      end
      Completion::Types::InstanceType.new Hash, K: Completion::Types::UnionType[*keys], V: Completion::Types::UnionType[*values]
    in [:hash, nil]
      Completion::Types::InstanceType.new Hash
    in [:paren | :ensure | :else, statements]
      statements.map { simulate_evaluate _1, scope }.last
    in [:const_path_ref, receiver, [:@const, name,]]
      r = simulate_evaluate receiver, scope
      (r in Completion::Types::SingletonType) ? self.class.type_of { r.module_or_class.const_get name } : Completion::Types::NIL
    in [:__var_ref_or_call, [type, name, pos]]
      sexp = scope.has?(name) ? [:var_ref, [type, name, pos]] : [:vcall, [:@ident, name, pos]]
      simulate_evaluate sexp, scope
    in [:var_ref, [:@kw, name,]]
      case name
      in 'self'
        scope.self_type
      in 'true'
        Completion::Types::TRUE
      in 'false'
        Completion::Types::FALSE
      in 'nil'
        Completion::Types::NIL
      end
    in [:var_ref, [:@const | :@ivar | :@cvar | :@gvar | :@ident, name,]]
      scope[name] || Completion::Types::NIL
    in [:const_ref, [:@const, name,]]
      scope[name] || Completion::Types::NIL
    in [:aref, receiver, args]
      receiver_type = simulate_evaluate receiver, scope if receiver
      args, kwargs, _block = retrieve_method_args args
      args_type = args.map do |arg|
        if arg in Completion::Types::Splat
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
      receiver, method, args, kwargs, block = retrieve_method_call sexp
      receiver_type = receiver ? simulate_evaluate(receiver, scope) : scope.self_type
      args_type = args.map do |arg|
        if arg in Completion::Types::Splat
          simulate_evaluate arg.item, scope
          nil # TODO: splat
        else
          simulate_evaluate arg, scope
        end
      end

      if block
        if block in [:symbol_literal, [:symbol, [:@ident, block_name,]]]
          call_block_proc = ->(args) do
            block_receiver, *rest = args
            block_receiver ? simulate_call(block_receiver || Completion::Types::OBJECT, block_name, rest, nil, nil) : Completion::Types::OBJECT
          end
        elsif block in [:do_block | :brace_block => type, block_var, body]
          block_var in [:block_var, params,]
          call_block_proc = ->(args) do
            result, breaks, nexts =  scope.conditional do
              @jumps.with :break, :next do
                if params
                  names = extract_param_names(params)
                else
                  names = (1..max_numbered_params(body)).map { "_#{_1}" }
                  params = [:params, names.map { [:@ident, _1, [0, 0]] }, nil, nil, nil, nil, nil, nil]
                end
                block_scope = Scope.new scope, names.zip(args).to_h { [_1, _2 || Completion::Types::NIL] }
                evaluate_assign_params params, args, block_scope
                block_scope.conditional { evaluate_param_defaults params, block_scope } if params
                if type == :do_block
                  simulate_evaluate body, block_scope
                else
                  body.map {
                    simulate_evaluate _1, block_scope
                  }.last
                end
              end
            end
            [Completion::Types::UnionType[result, nexts], breaks]
          end
        else
          _block_arg = simulate_evaluate block, block_scope
        end
      end
      simulate_call receiver_type, method, args_type, kwargs_type(kwargs, scope), call_block_proc
    in [:binary, a, Symbol => op, b]
      atype = simulate_evaluate a, scope
      case op
      when :'&&', :and
        btype = scope.conditional { simulate_evaluate b, scope }
        Completion::Types::UnionType[btype, Completion::Types::NIL, Completion::Types::FALSE]
      when :'||', :or
        btype = scope.conditional { simulate_evaluate b, scope }
        Completion::Types::UnionType[atype, btype]
      else
        btype = simulate_evaluate b, scope
        simulate_call atype, op, [btype], nil, nil
      end
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, scope), op, [], nil, nil
    in [:lambda, params, statements]
      params in [:paren, params]
      if @dig_targets.dig? statements
        @jumps.with :break, :next, :return do
          params in [:paren, params]
          block_scope = Scope.new scope, extract_param_names(params).to_h { [_1, Completion::Types::NIL] }
          evaluate_assign_params params, [], block_scope
          block_scope.conditional { evaluate_param_defaults params, block_scope }
          statements.each { simulate_evaluate _1, block_scope }
        end
      end
      Completion::Types::ProcType.new
    in [:assign, [:var_field, [:@gvar | :@ivar | :@cvar | :@ident | :@const, name,]], value]
      res = simulate_evaluate value, scope
      scope[name] = res
      res
    in [:assign, [:aref_field, receiver, key], value]
      simulate_evaluate receiver, scope
      args, kwargs, _block = retrieve_method_args key
      args.each do |arg|
        item = ((arg in Completion::Types::Splat) ? arg.item : arg)
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
      receiver = (target in [:var_field, *field]) ? [:var_ref, *field] : target
      simulate_evaluate [:assign, target, [:binary, receiver, op, value]], scope
    in [:assign, target, value]
      simulate_evaluate target, scope
      simulate_evaluate value, scope
    in [:massign, targets, value]
      rhs = simulate_evaluate value, scope
      evaluate_massign targets, rhs, scope
      rhs
    in [:mrhs_new_from_args | :mrhs_add_star,]
      values, = evaluate_mrhs sexp, scope
      Completion::Types::InstanceType.new Array, Elem: Completion::Types::UnionType[*values]
    in [:ifop, cond, tval, fval]
      simulate_evaluate cond, scope
      Completion::Types::UnionType[*scope.run_branches(
        -> { simulate_evaluate tval, scope },
        -> { simulate_evaluate fval, scope }
      )]
    in [:if_mod | :unless_mod, cond, statement]
      simulate_evaluate cond, scope
      Completion::Types::UnionType[scope.conditional { simulate_evaluate statement, scope }, Completion::Types::NIL]
    in [:if | :unless | :elsif, cond, statements, else_statement]
      simulate_evaluate cond, scope
      if_result, else_result = scope.run_branches(
        -> { statements.map { simulate_evaluate _1, scope }.last },
        -> { else_statement ? simulate_evaluate(else_statement, scope) : Completion::Types::NIL }
      )
      Completion::Types::UnionType[if_result, else_result]
    in [:while | :until, cond, statements]
      @jumps.with :break do
        simulate_evaluate cond, scope
        scope.conditional { statements.each { simulate_evaluate _1, scope } }
      end
      Completion::Types::NIL
    in [:while_mod | :until_mod, cond, statement]
      simulate_evaluate cond, scope
      scope.conditional { simulate_evaluate statement, scope }
      Completion::Types::NIL
    in [:break | :next | :return => jump_type, value]
      if value.empty?
        @jumps.send jump_type, Completion::Types::NIL
      else
        values, kw = evaluate_mrhs value, scope
        values << kw if kw
        @jumps.send jump_type, Completion::Types::InstanceType.new(Array, Elem: Completion::Types::UnionType[*values])
      end
      Completion::Types::NIL
    in [:return0]
      @jumps.return Completion::Types::NIL
    in [:begin, body_stmt]
      simulate_evaluate body_stmt, scope
    in [:bodystmt, statements, rescue_stmt, _unknown, ensure_stmt]
      return_type = statements.map { simulate_evaluate _1, scope }.last
      if rescue_stmt
        return_type = Completion::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_stmt, scope }]
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
          error_types = error_classes.filter_map { Completion::Types::InstanceType.new _1.module_or_class if _1 in Completion::Types::SingletonType }
          error_types << Completion::Types::InstanceType.new(StandardError) if error_types.empty?
          scope[error_var] = Completion::Types::UnionType[*error_types]
        end
        statements.map { simulate_evaluate _1, scope }.last
      end
      if rescue_stmt
        return_type = Completion::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_stmt, scope }]
      end
      return_type
    in [:rescue_mod, statement1, statement2]
      a = simulate_evaluate statement1, scope
      b = scope.conditional { simulate_evaluate statement2, scope }
      Completion::Types::UnionType[a, b]
    in [:module, module_stmt, body_stmt]
      module_types = simulate_evaluate(module_stmt, scope).types.grep(Completion::Types::SingletonType)
      module_types << Completion::Types::MODULE if module_types.empty?
      simulate_evaluate body_stmt, Scope.new(scope, { SELF => Completion::Types::UnionType[*module_types] }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
    in [:sclass, klass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope).types.filter_map do |type|
        Completion::Types::SingletonType.new type.klass if type in Completion::Types::InstanceType
      end
      klass_types = [Completion::Types::CLASS] if klass_types.empty?
      simulate_evaluate body_stmt, Scope.new(scope, { SELF => Completion::Types::UnionType[*klass_types] }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
    in [:class, klass_stmt, superclass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope).types
      klass_types += simulate_evaluate(superclass_stmt, scope).types if superclass_stmt
      klass_types = klass_types.select do |type|
        (type in Completion::Types::SingletonType) && type.module_or_class.is_a?(Class)
      end
      klass_types << Completion::Types::CLASS if klass_types.empty?
      simulate_evaluate body_stmt, Scope.new(scope, { SELF => Completion::Types::UnionType[*klass_types] }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
    in [:for, fields, enum, statements]
      fields = [fields] if fields in [:var_field,]
      params = [:params, fields, nil, nil, nil, nil, nil, nil]
      enum = simulate_evaluate enum, scope
      extract_param_names(params).each { scope[_1] = Completion::Types::NIL }
      response = simulate_call enum, :first, [], nil, nil
      evaluate_assign_params params, [response], scope
      scope.conditional do
        statements.each { simulate_evaluate _1, scope }
      end
      enum
    in [:in | :when => mode, pattern, if_statements, else_statement]
      if mode == :in
        if_match = -> { match_pattern case_target, pattern, scope }
        else_match = -> { scope.conditional { if_match.call } }
      else
        eval_pattern = lambda do |pattern, *rest|
          simulate_evaluate pattern, scope
          scope.conditional { eval_pattern.call(*rest) } if rest.any?
        end
        if_match = -> { eval_pattern.call(*pattern) }
        else_match = -> { pattern.each { simulate_evaluate _1, scope } }
      end
      if_branch = lambda do
        if_match.call
        if_statements.map { simulate_evaluate _1, scope }.last
      end
      else_branch = lambda do
        else_match.call
        simulate_evaluate(else_statement, scope, case_target:)
      end
      if if_statements && else_statement
        Completion::Types::UnionType[*scope.run_branches(if_branch, else_branch)]
      elsif if_statements
        Completion::Types::UnionType[scope.conditional { if_branch.call }, Completion::Types::NIL]
      elsif else_statement
        Completion::Types::UnionType[scope.conditional { else_branch.call }, Completion::Types::NIL]
      else
        Completion::Types::NIL
      end
    in [:case, target_exp, match_exp]
      target = simulate_evaluate target_exp, scope
      simulate_evaluate match_exp, scope, case_target: target
    in [:void_stmt]
      Completion::Types::NIL
    in [:dot2,]
      Completion::Types::RANGE
    else
      STDERR.cooked{
        STDERR.puts
        STDERR.puts :NOMATCH
        STDERR.puts sexp.inspect
      }
      Completion::Types::NIL
    end
  end

  def match_pattern(target, pattern, scope)
    types = target.types
    case pattern
    in [:var_field, [:@ident, name,]]
      scope[name] = target
    in [:var_ref,] # in Array, in ^a, in nil
    in [:@int | :@float | :@rational | :@imaginary | :@symbol_literal | :@string_literal | :@regexp_literal | :@CHAR,]
    in [:begin, statement] # in (statement)
      simulate_evaluate statement, scope
    in [:binary, lpattern, :'=>', [var_field, [:@ident, name,]]]
      if lpattern in [:var_ref, [:@const, const_name,]]
        const_value = simulate_evaluate lpattern, scope
        if (const_value in Completion::Types::SingletonType) && const_value.module_or_class.is_a?(Class)
          scope[name] = Completion::Types::InstanceType.new const_value.module_or_class
        else
          scope[name] = Completion::Types::OBJECT
        end
      else
        match_pattern target, lpattern, scope
        match_pattern target, rpattern, scope
      end
    in [:aryptn, _unknown, items, splat, post_items]
      # TODO: deconstruct keys
      array_types = types.select { (_1 in Completion::Types::InstanceType) && _1.klass == Array }
      elem = Completion::Types::UnionType[*array_types.filter_map { _1.params[:Elem] }]
      items&.each do |item|
        match_pattern elem, item, scope
      end
      if splat in [:var_field, [:@ident, name,]]
        scope[name] = Completion::Types::InstanceType.new Array, Elem: elem
      end
      post_items&.each do |item|
        match_pattern elem, item, scope
      end
    in [:hshptn, _unknown, items, splat]
      # TODO: deconstruct keys
      hash_types = types.select { (_1 in Completion::Types::InstanceType) && _1.klass == Hash }
      key_type = Completion::Types::UnionType[*hash_types.filter_map { _1.params[:K] }]
      value_type = Completion::Types::UnionType[*hash_types.filter_map { _1.params[:V] }]
      items&.each do |key_pattern, value_pattern|
        if key_pattern in [:@label, label,]
          name = label.delete ':'
          scope[name] = value_type unless value_pattern
        end
        match_pattern value_type, value_pattern, scope if value_pattern
      end
      if splat in [:var_field, [:@ident, name,]]
        scope[name] = Completion::Types::InstanceType.new Hash, K: key_type, V: value_type
      end
    else
      puts "Unimplemented match pattern: #{pattern}"
    end
  end

  def evaluate_mrhs(sexp, scope)
    args, kwargs, = retrieve_method_args sexp
    values = args.filter_map do |t|
      if t in Completion::Types::Splat
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
        in Completion::Types::Splat
          simulate_evaluate t.item, scope
          # TODO
          [Completion::Types::SYMBOL, Completion::Types::OBJECT]
        in [key, value]
          key_type = (key in [:@label,]) ? Completion::Types::SYMBOL : simulate_evaluate(key, scope)
          [key_type, simulate_evaluate(value, scope)]
        end
      end
      key_type = Completion::Types::UnionType[*kvs.map(&:first)]
      value_type = Completion::Types::UnionType[*kvs.map(&:last)]
      kw = Completion::Types::InstanceType.new(Hash, K: key_type, V: value_type)
    end
    [values, kw]
  end

  def evaluate_massign(sexp, values, scope)
    unless values in Array
      to_ary_result = simulate_call values, :to_ary, [], nil, nil, name_match: false
      values = to_ary_result if (to_ary_result in Completion::Types::InstanceType) && to_ary_result.klass == Array
      if (values in Completion::Types::InstanceType) && values.klass == Array
        values = [values.params[:Elem] || Completion::Types::OBJECT] * sexp.size
      else
        values = [values]
      end
    end

    rest_index = sexp.find_index { _1 in [:rest_param, ]}
    if rest_index
      pre = rest_index ? sexp[0...rest_index] : sexp
      post = rest_index ? sexp[rest_index + 1..] : []
      sexp[rest_index] in [:rest_param, rest_field]
      rest_values = values[pre.size...-post.size] || []
      rest_type = Completion::Types::InstanceType.new Array, Elem: Completion::Types::UnionType[*rest_values]
      pairs = pre.zip(values.first(pre.size)) + [[rest_field, rest_type]] + post.zip(values.last(post.size))
    else
      pairs = sexp.zip values
    end
    pairs.each do |field, value|
      case field
      in [:@ident, name,]
        # block arg mlhs
        scope[name] = value || Completion::Types::OBJECT
      in [:var_field, [:@ident, name,]]
        # massign
        scope[name] = value || Completion::Types::OBJECT
      in [:mlhs, *mlhs]
        evaluate_massign mlhs, value || [], scope
      end
    end
  end

  def kwargs_type(kwargs, scope)
    return if kwargs.empty?
    keys = []
    values = []
    kwargs.each do |kv|
      if kv in Completion::Types::Splat
        hash = simulate_evaluate kv.item, scope
        unless (hash in Completion::Types::InstanceType) && hash.klass == Hash
          hash = simulate_call hash, :to_hash, [], nil, nil
        end
        if (hash in Completion::Types::InstanceType) && hash.klass == Hash
          keys << hash.params[:K] if hash.params[:K]
          values << hash.params[:V] if hash.params[:V]
        end
      else
        key, value = kv
        keys << ((key in [:@label,]) ? Completion::Types::SYMBOL : simulate_evaluate(key, scope))
        values << simulate_evaluate(value, scope)
      end
    end
    Completion::Types::InstanceType.new(Hash, K: Completion::Types::UnionType[*keys], V: Completion::Types::UnionType[*values])
  end

  def self.type_of(fallback: Completion::Types::OBJECT)
    begin
      Completion::Types.type_from_object yield
    rescue
      fallback
    end
  end

  def retrieve_method_call(sexp)
    # TODO: &. conditional
    case sexp
    in [:fcall | :vcall, [:@ident | :@const | :@kw | :@op, method,]] # hoge
      [nil, method, [], [], false, nil]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', :call] # a.()
      [receiver, :call, [], [], false, nil]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const | :@kw | :@op, method,]] # a.hoge
      [receiver, method, [], [], false, nil]
    in [:command, [:@ident | :@const | :@kw | :@op, method,], args] # hoge 1, 2
      args, kwargs, block = retrieve_method_args args
      [nil, method, args, kwargs, block]
    in [:command_call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const | :@kw | :@op, method,], args] # a.hoge 1; a.hoge 1, 2;
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block]
    in [:method_add_arg, call, args]
      receiver, method = retrieve_method_call call
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block]
    in [:method_add_block, call, block]
      receiver, method, args, kwargs = retrieve_method_call call
      [receiver, method, args, kwargs, block]
    end
  end

  def retrieve_method_args(sexp)
    case sexp
    in [:mrhs_add_star, args, star]
      args, = retrieve_method_args args
      [[*args, Completion::Types::Splat.new(star)], [], nil]
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
      [args, kwargs, block_arg]
    in [:args_add_block, [*args, [:bare_assoc_hash,] => kw], block_arg]
      _, kwargs = retrieve_method_args kw
      [args, kwargs, block_arg]
    in [:args_add_block, [*args], block_arg]
      [args, [], block_arg]
    in [:bare_assoc_hash, kws]
      kwargs = []
      kws.each do |kw|
        if kw in [:assoc_splat, value,]
          kwargs << Completion::Types::Splat.new(value)
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
      args = [*pre_args, Completion::Types::Splat.new(star_arg), *post_args]
      [args, [], nil]
    in [:arg_paren, args]
      args ? retrieve_method_args(args) : [[], [], nil]
    else
      [[], [], nil]
    end
  end

  def simulate_call(receiver, method_name, args, kwargs, block, name_match: true)
    methods = Completion::Types.rbs_methods receiver, method_name.to_sym, args, kwargs, !!block
    block_called = false
    type_breaks = methods.map do |method, given_params, method_params|
      receiver_vars = (receiver in Completion::Types::InstanceType) ? receiver.params : {}
      free_vars = method.type.free_variables - receiver_vars.keys.to_set
      vars = receiver_vars.merge Completion::Types.match_free_variables(free_vars, method_params, given_params)
      if block && method.block
        params_type = method.block.type.required_positionals.map do |func_param|
          Completion::Types.from_rbs_type func_param.type, receiver, vars
        end
        block_response, breaks = block.call params_type
        block_called = true
        vars.merge! Completion::Types.match_free_variables(free_vars - vars.keys.to_set, [method.block.type.return_type], [block_response])
      end
      [Completion::Types.from_rbs_type(method.type.return_type, receiver, vars || {}), breaks]
    end
    block&.call [] unless block_called
    types = type_breaks.map(&:first)
    breaks = type_breaks.map(&:last).compact
    types << OBJECT_METHODS[method_name.to_sym] if name_match && OBJECT_METHODS.has_key?(method_name.to_sym)
    Completion::Types::UnionType[*types, *breaks]
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
    params => [:params, pre_required, optional, rest, post_required, keywords, keyrest, block]
    size = (pre_required&.size || 0) + (optional&.size || 0) + (post_required&.size || 0) + (rest ? 1 : 0)
    if values.size == 1 && size >= 2
      to_ary_result = simulate_call values.first || Completion::Types::OBJECT, :to_ary, [], nil, nil
      if (to_ary_result in Completion::Types::InstanceType) && to_ary_result.klass == Array
        values = [to_ary_result.params[:Elem] || Completion::Types::OBJECT] * size
      end
    end
    pre_values = values.shift pre_required.size if pre_required
    post_values = values.pop post_required.size if post_required
    opt_values = values.shift optional.size if optional
    rest_values = values
    evaluate_massign pre_required, pre_values, scope if pre_required
    evaluate_massign optional.map(&:first), opt_values, scope if optional
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = Completion::Types::InstanceType.new Array, Elem: Completion::Types::UnionType[*rest_values]
    end
    evaluate_massign post_required, post_values, scope if post_required
    if keyrest in [:kwrest_param, [:@ident, name,]]
      scope[name] = Completion::Types::InstanceType.new Hash, K: Completion::Types::SYMBOL, V: Completion::Types::OBJECT
    end
    if block in [:blockarg, [:@ident, name,]]
      scope[name] = Completion::Types::PROC
    end
  end

  def evaluate_param_defaults(params, scope)
    params => [:params, _pre_required, optional, rest, _post_required, keywords, keyrest, block]
    optional&.each do |item, value|
      item => [:@ident, name,]
      scope[name] = simulate_evaluate value, scope
    end
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = Completion::Types::ARRAY
    end
    keywords&.each do |key, value|
      key => [:@label, label,]
      name = label.delete ':'
      scope[name] = value ? simulate_evaluate(value, scope) : Completion::Types::OBJECT
    end
    if keyrest
      keyrest => [:kwrest_param, [:@ident, name,]]
      scope[name] = Completion::Types::HASH
    end
    if block
      block => [:blockarg, [:@ident, name,]]
      scope[name] = Completion::Types::PROC
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
    Completion::Types::NIL
  end
end
