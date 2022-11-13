require_relative 'types'
require 'ripper'
module Completion; end
module Completion::TypeSimulator

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
    end

    def mutable?() = false

    def [](name)
      @cache[name] ||= (
        case BaseScope.type_by_name name
        when :cvar
          Completion::TypeSimulator.type_of { @self_object.class_variable_get name }
        when :ivar
          Completion::TypeSimulator.type_of { @self_object.instance_variable_get name }
        else
          Completion::TypeSimulator.type_of { @binding.eval name }
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
      else
        :lvar
      end
    end
  end

  class Scope
    attr_reader :parent

    def self.from_binding(binding) = new BaseScope.new(binding, binding.eval('self'))

    def initialize(parent, trace_cvar: true, trace_ivar: true, trace_lvar: true)
      @tables = [{}]
      @parent = parent
      @trace_cvar = trace_cvar
      @trace_ivar = trace_ivar
      @trace_lvar = trace_lvar
    end

    def mutable?() = true

    def trace?(name)
      return false unless @parent
      type = BaseScope.type_by_name(name)
      type == :cvar ? @trace_cvar : type == :ivar ? @trace_ivar : @trace_lvar
    end

    def [](name)
      @tables.reverse_each do |table|
        return table[name] if table.has_key? name
      end
      @parent[name] if trace? name
    end

    def []=(name, types)
      if trace?(name) && @parent.mutable? && @parent.has?(name)
        @parent[name] = types
      else
        @tables.last[name] = types
      end
    end

    def start_conditional
      @tables << {}
    end

    def end_conditional
      changes = @tables.pop
      table = @tables.last
      changes.each do |key, value|
        table[key] = (table[key] || [NilClass]) | value
      end
    end

    def conditional
      scopes = [self]
      while scopes.last.parent&.mutable?
        scopes << scopes.last.parent
      end
      begin
        scopes.each(&:start_conditional)
        yield
      ensure
        scopes.each(&:end_conditional)
      end
    end

    def base_scope
      @parent&.mutable? ? @parent.base_scope : @parent
    end

    def has?(name)
      @table.has?(name) || (trace?(name) && @parent.has?(name))
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
    to_s: String,
    to_str: String,
    to_a: Array,
    to_ary: Array,
    to_h: Hash,
    to_hash: Hash,
    to_i: Integer,
    to_int: Integer,
    to_f: Float,
    to_c: Complex,
    to_r: Rational
  }

  def self.simulate_evaluate(sexp, scope, dig_targets)
    result = simulate_evaluate_inner(sexp, scope, dig_targets)
    dig_targets.resolve result if dig_targets.target?(sexp)
    result
  end

  def self.simulate_evaluate_inner(sexp, scope, dig_targets)
    case sexp
    in [:program, statements]
      statements.map { simulate_evaluate _1, scope, dig_targets }.last
    in [:def, *receiver, method, params, body_stmt]
      if dig_targets.dig? sexp
        simulate_evaluate body_stmt, Scope.new(scope, trace_lvar: false), dig_targets
      end
      [Symbol]
    in [:@int,]
      [Integer]
    in [:@float,]
      [Float]
    in [:@rational,]
      [Rational]
    in [:@imaginary,]
      [Complex]
    in [:symbol_literal | :dyna_symbol,]
      [Symbol]
    in [:string_literal | :@CHAR, ]
      [String]
    in [:regexp_literal,]
      [Regexp]
    in [:array, statements]
      statements.each { simulate_evaluate _1, scope, dig_targets }
      [Array]
    in [:hash,]
      [Hash]
    in [:paren | :ensure | :else, statements]
      statements.map { simulate_evaluate _1, scope, dig_targets }.last
    in [:const_path_ref, receiver, [:@const, name,]]
      simulate_evaluate(receiver, scope, dig_targets).flat_map do |k|
        (k in { class: klass }) ? type_of { klass.const_get name } : []
      end
    in [:var_ref, [:@kw, name,]]
      klass = { 'true' => TrueClass, 'false' => FalseClass, 'nil' => NilClass }[name]
      [*klass]
    in [:var_ref, [:@const | :@ivar | :@cvar | :@gvar | :@ident, name,]]
      scope[name] || []
    in [:aref, receiver, args]
      receiver_type = simulate_evaluate receiver, scope, dig_targets if receiver
      args, kwargs, kwsplat, block = retrieve_method_args args
      args_type = args.map { simulate_evaluate _1, scope, dig_targets if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, scope, dig_targets }
      simulate_call receiver_type, :[], args_type, kwargs_type, kwsplat, block
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      receiver, method, args, kwargs, kwsplat, block = retrieve_method_call sexp
      receiver_type = simulate_evaluate receiver, scope, dig_targets if receiver
      args_type = args.map { simulate_evaluate _1, scope, dig_targets if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, scope, dig_targets }
      if dig_targets.dig?(block) && (block in [:do_block | :brace_block, params, body_stmt])
        simulate_evaluate body_stmt, scope, dig_targets
      end
      simulate_call receiver_type, method, args_type, kwargs_type, kwsplat, !!block
    in [:binary, a, Symbol => op, b]
      atypes, btypes = [a, b].map { simulate_evaluate _1, scope, dig_targets }
      case op
      when :'&&', :and
        truthy = atypes - [NilClass, FalseClass]
        falsy = atypes & [NilClass, FalseClass]
        if truthy.empty?
          falsy
        else
          falsy | btypes
        end
      when :'||', :or
        truthy = atypes - [NilClass, FalseClass]
        falsy = atypes & [NilClass, FalseClass]
        if falsy.empty?
          atypes
        else
          truthy | btypes
        end
      else
        simulate_call atypes, op, [btypes], {}, false, false
      end
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, scope, dig_targets), op, [], {}, false, false
    in [:lambda, params, statements]
      if dig_targets.dig? statements
        statements.each { simulate_evaluate _1, scope, dig_targets }
      end
      [Proc]
    in [:assign, [:var_field, [:@gvar | :@ivar | :@cvar | :@ident, name,]], value]
      res = simulate_evaluate value, scope, dig_targets
      scope[name] = res
      res
    in [:massign | :assign, _target, value]
      simulate_evaluate value, scope, dig_targets
    in [:mrhs_new_from_args,]
      [Array]
    in [:ifop, cond, tval, fval]
      simulate_evaluate cond, scope, dig_targets
      scope.conditional { simulate_evaluate tval, scope, dig_targets } | scope.conditional { simulate_evaluate fval, scope, dig_targets }
    in [:if_mod | :unless_mod, cond, statement]
      simulate_evaluate cond, scope, dig_targets
      scope.conditional { simulate_evaluate statement, scope, dig_targets } | [NilClass]
    in [:if | :unless | :elsif, cond, statements, else_statement]
      simulate_evaluate cond, scope, dig_targets
      type1 = scope.conditional do
        statements.map { simulate_evaluate _1, scope, dig_targets }.last
      end
      if else_statement
        type1 | scope.conditional { simulate_evaluate else_statement, scope, dig_targets }
      else
        type1 | [NilClass]
      end
    in [:while | :until, cond, statements]
      simulate_evaluate cond, scope, dig_targets
      scope.conditional { statements.each { simulate_evaluate _1, scope, dig_targets } }
      [NilClass]
    in [:while_mod | :until_mod, cond, statement]
      simulate_evaluate cond, scope, dig_targets
      scope.conditional { simulate_evaluate statement, scope, dig_targets }
      [NilClass]
    in [:begin, body_stmt]
      simulate_evaluate body_stmt, scope, dig_targets
    in [:bodystmt, statements, rescue_stmt, _unknown, ensure_stmt]
      return_type = statements.map { simulate_evaluate _1, scope, dig_targets }.last
      if rescue_stmt
        return_type |= scope.conditional { simulate_evaluate rescue_stmt, scope, dig_targets }
      end
      simulate_evaluate ensure_stmt, scope, dig_targets if ensure_stmt
      return_type
    in [:rescue, error_class_stmts, error_var_stmt, statements, rescue_stmt]
      return_type = scope.conditional do
        if error_var_stmt in [:var_field, [:@ident, error_var,]]
          error_classes = (error_class_stmts || []).flat_map { simulate_evaluate _1, scope, dig_targets }.uniq
          error_types = error_classes.filter_map { (_1 in { class: klass }) && klass }
          error_types = [StandardError] if error_types.empty?
          scope[error_var] = error_types
        end
        statements.map { simulate_evaluate _1, scope, dig_targets }.last
      end
      if rescue_stmt
        return_type |= simulate_evaluate rescue_stmt, scope, dig_targets
      end
      return_type
    in [:rescue_mod, statement1, statement2]
      a = simulate_evaluate statement1, scope, dig_targets
      b = scope.conditional { simulate_evaluate statement2, scope, dig_targets }
      a | b
    in [:module, module_stmt, body_stmt]
      return [] unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), dig_targets
    in [:sclass, klass_stmt, body_stmt]
      return [] unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), dig_targets
    in [:class, klass_stmt, _superclass_stmt, body_stmt]
      return [] unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), dig_targets
    in [:case | :begin | :for | :class | :sclass | :module,]
      []
    in [:void_stmt]
      [NilClass]
    in [:dot2,]
      [Range]
    else
      STDERR.cooked{
        STDERR.puts
        STDERR.puts :NOMATCH
        STDERR.puts sexp.inspect
      }
      []
    end
  end

  def self.type_of
    begin
      value = yield
      value.is_a?(Module) ? [{ class: value }] : [value.class]
    rescue
      []
    end
  end

  def self.retrieve_method_call(sexp)
    case sexp
    in [:fcall | :vcall, [:@ident | :@const | :@kw | :@op, method,]] # hoge
      [nil, method, [], {}, false, nil]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', :call] # a.()
      [receiver, :call, [], {}, false, nil]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const | :@kw | :@op, method,]] # a.hoge
      [receiver, method, [], {}, false, nil]
    in [:command, [:@ident | :@const | :@kw | :@op, method,], args] # hoge 1, 2
      args, kwargs, kwsplat, block = retrieve_method_args args
      [nil, method, args, kwargs, kwsplat, block]
    in [:command_call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const | :@kw | :@op, method,], args] # a.hoge 1; a.hoge 1, 2;
      args, kwargs, kwsplat, block = retrieve_method_args args
      [receiver, method, args, kwargs, kwsplat, block]
    in [:method_add_arg, call, args]
      receiver, method = retrieve_method_call call
      args, kwargs, kwsplat, block = retrieve_method_args args
      [receiver, method, args, kwargs, kwsplat, block]
    in [:method_add_block, call, block]
      receiver, method, args, kwargs, kwsplat = retrieve_method_call call
      [receiver, method, args, kwargs, kwsplat, block]
    end
  end

  def self.retrieve_method_args(sexp)
    case sexp
    in [:args_add_block, [:args_add_star,] => args, block_arg]
      args, = retrieve_method_args args
      [args, {}, false, block_arg]
    in [:args_add_block, [*args, [:bare_assoc_hash,] => kwargs], block_arg]
      args, = retrieve_method_args args
      _, kwargs, kwsplat = retrieve_method_args kwargs
      [args, kwargs, kwsplat, block_arg]
    in [:args_add_block, [*args], block_arg]
      [args, {}, false, block_arg]
    in [:bare_assoc_hash, kws]
      kwargs = {}
      kwsplat = false
      kws.each do |kw|
        if kw in [:assoc_splat, *rest]
          kwsplat = true
        elsif kw in [:assoc_new, [:@label, label,], value]
          key = label.delete ':'
          kwargs[key] = value || [:var_ref, [key =~ /\A[A-Z]/ ? :@const : :@ident, key, [0, 0]]]
        end
      end
      [[], kwargs, kwsplat, nil]
    in [:args_add_star, *args, [:bare_assoc_hash,] => kwargs]
      args, = retrieve_method_args [:args_add_star, *args]
      _, kwargs, kwsplat = retrieve_method_args kwargs
      [args, kwargs, kwsplat, nil]
    in [:args_add_star, pre_args, star_arg, *post_args]
      pre_args, = retrieve_method_args pre_args if pre_args in [:args_add_star,]
      args = [*pre_args, nil, *post_args]
      [args, {}, false, nil]
    in [:arg_paren, args]
      args ? retrieve_method_args(args) : [[], {}, false, nil]
    else
      [[], {}, false, nil]
    end
  end

  def self.simulate_call(receiver, method, args, kwargs, kwsplat, has_block)
    receiver ||= [{ class: Kernel }]
    result = receiver.flat_map do |klass|
      Completion::Types.rbs_method_response klass, method.to_sym, args, kwargs, kwsplat, has_block
    end.uniq
    result |= [OBJECT_METHODS[method.to_sym]] if OBJECT_METHODS.has_key? method.to_sym
    result.empty? ? [Object, NilClass] : result
  end

  def self.calculate_receiver(binding, parents, receiver)
    dig_targets = DigTarget.new(parents, receiver) do |types|
      return types
    end
    simulate_evaluate parents[0], Scope.from_binding(binding), dig_targets
    []
  end
end
