require_relative 'types'
require 'ripper'
require 'set'

module Completion; end
module Completion::TypeSimulator
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
    def resolve(types)
      @block.call types
    end
  end

  class BaseScope
    def initialize(binding, self_object)
      @binding, @self_object = binding, self_object
      @cache = {}
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

    def []=(name, types)
      if trace?(name) && @parent.mutable? && !@tables.any? { _1.key? name } && @parent.has?(name)
        @parent[name] = types
      else
        @tables.last[name] = types
      end
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

  def self.simulate_evaluate(sexp, scope, jumps, dig_targets)
    result = simulate_evaluate_inner(sexp, scope, jumps, dig_targets)
    dig_targets.resolve result if dig_targets.target?(sexp)
    result
  end

  def self.simulate_evaluate_inner(sexp, scope, jumps, dig_targets)
    case sexp
    in [:program, statements]
      statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
    in [:def, *receiver, method, params, body_stmt]
      if dig_targets.dig? sexp
        # TODO: method args
        simulate_evaluate body_stmt, Scope.new(scope, trace_lvar: false), jumps, dig_targets
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
    in [:symbol_literal | :dyna_symbol,]
      Completion::Types::SYMBOL
    in [:string_literal | :@CHAR, ]
      Completion::Types::STRING
    in [:regexp_literal,]
      Completion::Types::REGEXP
    in [:array, [:args_add_star,] => star]
      args, kwargs = retrieve_method_args star
      types = args.flat_map do |elem|
        if elem in Completion::Types::Splat
          splat = simulate_evaluate elem.item, scope, jumps, dig_targets
          unless (splat in Completion::Types::InstanceType) && splat.klass == Array
            to_a_result = simulate_call splat, :to_a, [], nil, nil
            splat = to_a_result if (to_a_result in Completion::Types::InstanceType) && splat.klass == Array
          end
          if (splat in Completion::Types::InstanceType) && splat.klass == Array
            splat.params[:Elem] || []
          else
            splat
          end
        else
          simulate_evaluate elem, scope, jumps, dig_targets
        end
      end
      types << kwargs_type(kwargs, scope, jumps, dig_targets) if kwargs && kwargs.any?
      Completion::Types::InstanceType.new Array, Elem: Completion::Types::UnionType[*types]
    in [:array, statements]
      elem = statements ? Completion::Types::UnionType[*statements.map { simulate_evaluate _1, scope, jumps, dig_targets }] : Completion::Types::NIL
      Completion::Types::InstanceType.new Array, Elem: elem
    in [:bare_assoc_hash, args]
      simulate_evaluate [:hash, [:assoclist_from_args, args]], scope, jumps, dig_targets
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
            keys << simulate_evaluate(key, scope, jumps, dig_targets)
          end
          values << simulate_evaluate(value, scope, jumps, dig_targets)
        in [:assoc_splat, value]
          hash = simulate_evaluate value, scope, jumps, dig_targets
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
      statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
    in [:const_path_ref, receiver, [:@const, name,]]
      r = simulate_evaluate receiver, scope, jumps, dig_targets
      (r in Completion::Types::SingletonType) ? type_of { r.module_or_class.const_get name } : Completion::Types::NIL
    in [:__var_ref_or_call, [type, name, pos]]
      sexp = scope.has?(name) ? [:var_ref, [type, name, pos]] : [:vcall, [:@ident, name, pos]]
      simulate_evaluate sexp, scope, jumps, dig_targets
    in [:var_ref, [:@kw, name,]]
      case name
      in 'self'
        # TODO
        Completion::Types::OBJECT
      in 'true'
        Completion::Types::TRUE
      in 'false'
        Completion::Types::FALSE
      in 'nil'
        Completion::Types::NIL
      end
    in [:var_ref, [:@const | :@ivar | :@cvar | :@gvar | :@ident, name,]]
      scope[name] || Completion::Types::NIL
    in [:aref, receiver, args]
      receiver_type = simulate_evaluate receiver, scope, jumps, dig_targets if receiver
      args, kwargs, _block = retrieve_method_args args
      args_type = args.map { simulate_evaluate _1, scope, jumps, dig_targets if _1 }
      simulate_call receiver_type, :[], args_type, kwargs_type(kwargs, scope, jumps, dig_targets), nil
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      receiver, method, args, kwargs, block = retrieve_method_call sexp
      receiver_type = simulate_evaluate receiver, scope, jumps, dig_targets if receiver
      args_type = args.map { simulate_evaluate _1, scope, jumps, dig_targets if _1 }
      if block
        if block in [:symbol_literal, [:symbol, [:@ident, block_name,]]]
          call_block_proc = ->(args) do
            block_receiver, *rest = args
            block_receiver ? simulate_call(block_receiver, block_name, rest, nil, nil) : Completion::Types::OBJECT
          end
        elsif block in [:do_block | :brace_block => type, block_var, body]
          block_var in [:block_var, params,]
          call_block_proc = ->(args) do
            result, breaks, nexts =  scope.conditional do
              jumps.with :break, :next do
                if params
                  names = extract_param_names(params)
                else
                  names = (1..max_numbered_params(body)).map { "_#{_1}" }
                  params = [:params, names.map { [:@ident, _1, [0, 0]] }, nil, nil, nil, nil, nil, nil]
                end
                # TODO: params match
                block_scope = Scope.new scope, names.zip(args).to_h { [_1, _2 || Completion::Types::NIL] }
                block_scope.conditional { evaluate_param_defaults params, block_scope, jumps, dig_targets } if params
                if type == :do_block
                  simulate_evaluate body, block_scope, jumps, dig_targets
                else
                  body.map {
                    simulate_evaluate _1, block_scope, jumps, dig_targets
                  }.last
                end
              end
            end
            [Completion::Types::UnionType[result, nexts], breaks]
          end
        else
          _block_arg = simulate_evaluate block, block_scope, jumps, dig_targets
        end
      end
      simulate_call receiver_type, method, args_type, kwargs_type(kwargs, scope, jumps, dig_targets), call_block_proc
    in [:binary, a, Symbol => op, b]
      atype = simulate_evaluate a, scope, jumps, dig_targets
      case op
      when :'&&', :and
        btype = scope.conditional { simulate_evaluate b, scope, jumps, dig_targets }
        Completion::Types::UnionType[btype, Completion::Types::NIL, Completion::Types::FALSE]
      when :'||', :or
        btype = scope.conditional { simulate_evaluate b, scope, jumps, dig_targets }
        Completion::Types::UnionType[atype, btype]
      else
        btype = simulate_evaluate b, scope, jumps, dig_targets
        simulate_call atype, op, [btype], nil, nil
      end
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, scope, jumps, dig_targets), op, [], nil, nil
    in [:lambda, params, statements]
      params in [:paren, params]
      if dig_targets.dig? statements
        jumps.with :break, :next, :return do
          block_scope = Scope.new scope, {} # TODO: with block params
          statements.each { simulate_evaluate _1, block_scope, jumps, dig_targets }
        end
      end
      Completion::Types::ProcType.new
    in [:assign, [:var_field, [:@gvar | :@ivar | :@cvar | :@ident, name,]], value]
      res = simulate_evaluate value, scope, jumps, dig_targets
      scope[name] = res
      res
    in [:opassign, target, [:@op, op,], value]
      op = op.to_s.delete('=').to_sym
      receiver = (target in [:var_field, *field]) ? [:var_ref, *field] : target
      simulate_evaluate [:assign, target, [:binary, receiver, op, value]], scope, jumps, dig_targets
    in [:assign, target, value]
      simulate_evaluate target, scope, jumps, dig_targets
      simulate_evaluate value, scope, jumps, dig_targets
    in [:massign, targets, value]
      # TODO
      simulate_evaluate value, scope, jumps, dig_targets
    in [:mrhs_new_from_args,]
      # TODO
      Completion::Types::InstanceType.new Array
    in [:ifop, cond, tval, fval]
      simulate_evaluate cond, scope, jumps, dig_targets
      Completion::Types::UnionType[*scope.run_branches(
        -> { simulate_evaluate tval, scope, jumps, dig_targets },
        -> { simulate_evaluate fval, scope, jumps, dig_targets }
      )]
    in [:if_mod | :unless_mod, cond, statement]
      simulate_evaluate cond, scope, jumps, dig_targets
      Completion::Types::UnionType[scope.conditional { simulate_evaluate statement, scope, jumps, dig_targets }, Completion::Types::NIL]
    in [:if | :unless | :elsif, cond, statements, else_statement]
      simulate_evaluate cond, scope, jumps, dig_targets
      if_result, else_result = scope.run_branches(
        -> { statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last },
        -> { else_statement ? simulate_evaluate(else_statement, scope, jumps, dig_targets) : Completion::Types::NIL }
      )
      Completion::Types::UnionType[if_result, else_result]
    in [:while | :until, cond, statements]
      jumps.with :break do
        simulate_evaluate cond, scope, jumps, dig_targets
        scope.conditional { statements.each { simulate_evaluate _1, scope, jumps, dig_targets } }
      end
      Completion::Types::NIL
    in [:while_mod | :until_mod, cond, statement]
      simulate_evaluate cond, scope, jumps, dig_targets
      scope.conditional { simulate_evaluate statement, scope, jumps, dig_targets }
      Completion::Types::NIL
    in [:break | :next | :return => jump_type, value]
      if value.empty?
        jumps.send jump_type, Completion::Types::NIL
      else
        args, kwargs, = retrieve_method_args value
        types = args.filter_map do |t|
          if t in Completion::Types::Splat
            # TODO
          else
            simulate_evaluate t, scope, jumps, dig_targets
          end
        end
        # TODO: kwargs
        jumps.send jump_type, Completion::Types::UnionType[*types]
      end
      Completion::Types::NIL
    in [:return0]
      jumps.return Completion::Types::NIL
    in [:begin, body_stmt]
      simulate_evaluate body_stmt, scope, jumps, dig_targets
    in [:bodystmt, statements, rescue_stmt, _unknown, ensure_stmt]
      return_type = statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
      if rescue_stmt
        return_type = Completion::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_stmt, scope, jumps, dig_targets }]
      end
      simulate_evaluate ensure_stmt, scope, jumps, dig_targets if ensure_stmt
      return_type
    in [:rescue, error_class_stmts, error_var_stmt, statements, rescue_stmt]
      return_type = scope.conditional do
        if error_var_stmt in [:var_field, [:@ident, error_var,]]
          if (error_class_stmts in [:mrhs_new_from_args, Array => stmts, stmt])
            error_class_stmts = [*stmts, stmt]
          end
          error_classes = (error_class_stmts || []).flat_map { simulate_evaluate _1, scope, jumps, dig_targets }.uniq
          error_types = error_classes.filter_map { Completion::Types::InstanceType.new _1.module_or_class if _1 in Completion::Types::SingletonType }
          error_types << Completion::Types::InstanceType.new(StandardError) if error_types.empty?
          scope[error_var] = Completion::Types::UnionType[*error_types]
        end
        statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
      end
      if rescue_stmt
        return_type = Completion::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_stmt, scope, jumps, dig_targets }]
      end
      return_type
    in [:rescue_mod, statement1, statement2]
      a = simulate_evaluate statement1, scope, jumps, dig_targets
      b = scope.conditional { simulate_evaluate statement2, scope, jumps, dig_targets }
      Completion::Types::UnionType[a, b]
    in [:module, module_stmt, body_stmt]
      return Completion::Types::NIL unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), jumps, dig_targets
    in [:sclass, klass_stmt, body_stmt]
      return Completion::Types::NIL unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), jumps, dig_targets
    in [:class, klass_stmt, _superclass_stmt, body_stmt]
      return Completion::Types::NIL unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), jumps, dig_targets
    in [:case | :begin | :for | :class | :sclass | :module,]
      Completion::Types::NIL
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

  def self.kwargs_type(kwargs, scope, jumps, dig_targets)
    return if kwargs.empty?
    keys = []
    values = []
    kwargs.each do |kv|
      if kv in Completion::Types::Splat
        hash = simulate_evaluate kv.item, scope, jumps, dig_targets
        unless (hash in Completion::Types::InstanceType) && hash.klass == Hash
          hash = simulate_call hash, :to_hash, [], nil, nil
        end
        if (hash in Completion::Types::InstanceType) && hash.klass == Hash
          keys << hash.params[:K] if hash.params[:K]
          values << hash.params[:V] if hash.params[:V]
        end
      else
        key, value = kv
        keys << ((key in [:@label,]) ? Completion::Types::SYMBOL : simulate_evaluate(key, scope, jumps, dig_targets))
        values << simulate_evaluate(value, scope, jumps, dig_targets)
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

  def self.retrieve_method_call(sexp)
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

  def self.retrieve_method_args(sexp)
    case sexp
    in [:args_add_block, [:args_add_star,] => args, block_arg]
      args, = retrieve_method_args args
      [args, [], block_arg]
    in [:args_add_block, [*args, [:bare_assoc_hash,] => kw], block_arg]
      args, = retrieve_method_args args
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

  def self.simulate_call(receiver, method, args, kwargs, block)
    receiver ||= Completion::Types::SingletonType.new(Kernel) # TODO: self
    methods = Completion::Types.rbs_methods receiver, method.to_sym, args, kwargs, !!block
    block_called = false
    type_breaks = methods.map do |method, given_params, method_params|
      receiver_vars = receiver.respond_to?(:params) ? receiver.params : {}
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
    types << OBJECT_METHODS[method.to_sym] if OBJECT_METHODS.has_key? method.to_sym
    Completion::Types::UnionType[*types, *breaks]
  end

  def self.extract_param_names(params)
    params => [:params, pre_required, optional, rest, post_required, keywords, keyrest, block]
    names = []
    extract_mlhs = ->(item) do
      case item
      in [:@ident, name,]
        names << name
      in [:mlhs, *items]
        items.each(&extract_mlhs)
      in [:rest_param, item]
        extract_mlhs.call item if item
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

  def self.evaluate_param_defaults(params, scope, jumps, dig_targets)
    params => [:params, _pre_required, optional, rest, _post_required, keywords, keyrest, block]
    optional&.each do |item, value|
      item => [:@ident, name,]
      scope[name] = simulate_evaluate value, scope, jumps, dig_targets
    end
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = Completion::Types::ARRAY
    end
    keywords&.each do |key, value|
      key => [:@label, label,]
      name = label.delete ':'
      scope[name] = value ? simulate_evaluate(value, scope, jumps, dig_targets) : Completion::Types::OBJECT
    end
    if keyrest
      keyerst => [:kwrest_param, [:@ident, name,]]
      scope[name] = Completion::Types::HASH
    end
    if block
      block => [:blockarg, [:@ident, name,]]
      scope[name] = Completion::Types::PROC
    end
  end

  def self.max_numbered_params(sexp)
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

  def self.calculate_receiver(binding, parents, receiver)
    jumps = JumpPoints.new
    dig_targets = DigTarget.new(parents, receiver) do |types|
      return types
    end
    simulate_evaluate parents[0], Scope.from_binding(binding), jumps, dig_targets
    Completion::Types::NIL
  end
end
