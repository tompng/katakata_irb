require_relative 'types'
require 'ripper'
module Completion; end
module Completion::TypeSimulator
  class JumpPoints
    def initialize
      @returns = []
      @breaks = []
    end
    def return(value) = @returns.last&.<< value
    def break(value) = @breaks.last&.<< value

    def with(*types)
      accumulators = types.map do |type|
        ac = []
        case type
        in :return
          @returns << ac
        in :break
          @breaks << ac
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
    end

    def mutable?() = false

    def [](name)
      @cache[name] ||= (
        fallback = Completion::Types::NilType
        case BaseScope.type_by_name name
        when :cvar
          Completion::TypeSimulator.type_of(fallback:) { @self_object.class_variable_get name }
        when :ivar
          Completion::TypeSimulator.type_of(fallback:) { @self_object.instance_variable_get name }
        else
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
      else
        :lvar
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
      type == :cvar ? @trace_cvar : type == :ivar ? @trace_ivar : @trace_lvar
    end

    def [](name)
      @tables.reverse_each do |table|
        return table[name] if table.key? name
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

  def self.simulate_evaluate(sexp, scope, jumps, dig_targets)
    result = simulate_evaluate_inner(sexp, scope, jumps, dig_targets)
    dig_targets.resolve result if dig_targets.target?(sexp)
    result
  end

  def self.simulate_proc_response(body, args_table, scope, jumps, dig_targets)
    proc_scope = Scope.new(scope, args_table)
    result, breaks = jumps.with :break do
      simulate_evaluate body, proc_scope, jumps, dig_targets
    end
    Completion::Types::UnionType[result, breaks]
  end

  def self.simulate_evaluate_inner(sexp, scope, jumps, dig_targets)
    case sexp
    in [:program, statements]
      statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
    in [:def, *receiver, method, params, body_stmt]
      if dig_targets.dig? sexp
        simulate_evaluate body_stmt, Scope.new(scope, trace_lvar: false), jumps, dig_targets
      end
      Completion::Types::InstanceType.new Symbol
    in [:@int,]
      Completion::Types::InstanceType.new Integer
    in [:@float,]
      Completion::Types::InstanceType.new Float
    in [:@rational,]
      Completion::Types::InstanceType.new Rational
    in [:@imaginary,]
      Completion::Types::InstanceType.new Complex
    in [:symbol_literal | :dyna_symbol,]
      Completion::Types::InstanceType.new Symbol
    in [:string_literal | :@CHAR, ]
      Completion::Types::InstanceType.new String
    in [:regexp_literal,]
      Completion::Types::InstanceType.new Regexp
    in [:array, statements]
      elem = statements ? Completion::Types::UnionType[*statements.map { simulate_evaluate _1, scope, jumps, dig_targets }] : Completion::Types::NilType
      Completion::Types::InstanceType.new Array, Elem: elem
    in [:hash,]
      # TODO
      Completion::Types::InstanceType.new Hash
    in [:paren | :ensure | :else, statements]
      statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
    in [:const_path_ref, receiver, [:@const, name,]]
      r = simulate_evaluate(receiver, scope, jumps, dig_targets)
      (r in Completion::Types::SingletonType) ? type_of { r.module_or_class.const_get name } : Completion::Types::NilType
    in [:var_ref, [:@kw, name,]]
      klass = { 'true' => TrueClass, 'false' => FalseClass, 'nil' => NilClass }[name]
      Completion::Types::InstanceType.new klass
    in [:var_ref, [:@const | :@ivar | :@cvar | :@gvar | :@ident, name,]]
      scope[name] || Completion::Types::NilType
    in [:aref, receiver, args]
      receiver_type = simulate_evaluate receiver, scope, jumps, dig_targets if receiver
      args, kwargs, kwsplat, block = retrieve_method_args args
      args_type = args.map { simulate_evaluate _1, scope, jumps, dig_targets if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, scope, jumps, dig_targets }
      simulate_call receiver_type, :[], args_type, kwargs_type, kwsplat, block
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      receiver, method, args, kwargs, kwsplat, block = retrieve_method_call sexp
      receiver_type = simulate_evaluate receiver, scope, jumps, dig_targets if receiver
      args_type = args.map { simulate_evaluate _1, scope, jumps, dig_targets if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, scope, jumps, dig_targets }
      if block
        block => [:do_block | :brace_block => type, params, body]
        result, breaks =  scope.conditional do
          jumps.with :break do
            block_scope = Scope.new scope, {} # TODO: with block params
            if type == :do_block
              simulate_evaluate body, block_scope, jumps, dig_targets
            else
              body.map {
                simulate_evaluate _1, block_scope, jumps, dig_targets
              }.last
            end
          end
        end
        proc_response = Completion::Types::UnionType[result, breaks]
      end
      simulate_call receiver_type, method, args_type, kwargs_type, kwsplat, !!block
    in [:binary, a, Symbol => op, b]
      atype = simulate_evaluate a, scope, jumps, dig_targets
      case op
      when :'&&', :and
        btype = scope.conditional { simulate_evaluate b, scope, jumps, dig_targets }
        Completion::Types::UnionType[btype, Completion::Types::NilType, Completion::Types::InstanceType.new(FalseClass)]
      when :'||', :or
        btype = scope.conditional { simulate_evaluate b, scope, jumps, dig_targets }
        Completion::Types::UnionType[atype, btype]
      else
        btype = simulate_evaluate b, scope, jumps, dig_targets
        simulate_call atype, op, [btype], {}, false, false
      end
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, scope, jumps, dig_targets), op, [], {}, false, false
    in [:lambda, params, statements]
      if dig_targets.dig? statements
        jump.with_return_point do
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
      Completion::Types::InstanceType.new Array
    in [:ifop, cond, tval, fval]
      simulate_evaluate cond, scope, jumps, dig_targets
      Completion::Types::UnionType[*scope.run_branches(
        -> { simulate_evaluate tval, scope, jumps, dig_targets },
        -> { simulate_evaluate fval, scope, jumps, dig_targets }
      )]
    in [:if_mod | :unless_mod, cond, statement]
      simulate_evaluate cond, scope, jumps, dig_targets
      Completion::Types::UnionType[scope.conditional { simulate_evaluate statement, scope, jumps, dig_targets }, Completion::Types::NilType]
    in [:if | :unless | :elsif, cond, statements, else_statement]
      simulate_evaluate cond, scope, jumps, dig_targets
      if_result, else_result = scope.run_branches(
        -> { statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last },
        -> { else_statement ? simulate_evaluate(else_statement, scope, jumps, dig_targets) : Completion::Types::NilType }
      )
      Completion::Types::UnionType[if_result, else_result]
    in [:while | :until, cond, statements]
      jumps.with :break do
        simulate_evaluate cond, scope, jumps, dig_targets
        scope.conditional { statements.each { simulate_evaluate _1, scope, jumps, dig_targets } }
      end
      Completion::Types::NilType
    in [:while_mod | :until_mod, cond, statement]
      simulate_evaluate cond, scope, jumps, dig_targets
      scope.conditional { simulate_evaluate statement, scope, jumps, dig_targets }
      Completion::Types::NilType
    in [:begin, body_stmt]
      simulate_evaluate body_stmt, scope, jumps, dig_targets
    in [:bodystmt, statements, rescue_stmt, _unknown, ensure_stmt]
      return_type = statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
      if rescue_stmt
        return_type |= scope.conditional { simulate_evaluate rescue_stmt, scope, jumps, dig_targets }
      end
      simulate_evaluate ensure_stmt, scope, jumps, dig_targets if ensure_stmt
      return_type
    in [:rescue, error_class_stmts, error_var_stmt, statements, rescue_stmt]
      return_type = scope.conditional do
        if error_var_stmt in [:var_field, [:@ident, error_var,]]
          error_classes = (error_class_stmts || []).flat_map { simulate_evaluate _1, scope, jumps, dig_targets }.uniq
          error_types = error_classes.filter_map { (_1 in { class: klass }) && klass }
          error_types = [StandardError] if error_types.empty?
          scope[error_var] = error_types
        end
        statements.map { simulate_evaluate _1, scope, jumps, dig_targets }.last
      end
      if rescue_stmt
        return_type |= simulate_evaluate rescue_stmt, scope, jumps, dig_targets
      end
      return_type
    in [:rescue_mod, statement1, statement2]
      a = simulate_evaluate statement1, scope, jumps, dig_targets
      b = scope.conditional { simulate_evaluate statement2, scope, jumps, dig_targets }
      Completion::Types::UnionType[a, b]
    in [:module, module_stmt, body_stmt]
      return Completion::Types::NilType unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), jumps, dig_targets
    in [:sclass, klass_stmt, body_stmt]
      return Completion::Types::NilType unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), jumps, dig_targets
    in [:class, klass_stmt, _superclass_stmt, body_stmt]
      return Completion::Types::NilType unless dig_targets.dig?(body_stmt)
      simulate_evaluate body_stmt, Scope.new(scope, trace_cvar: false, trace_ivar: false, trace_lvar: false), jumps, dig_targets
    in [:case | :begin | :for | :class | :sclass | :module,]
      Completion::Types::NilType
    in [:void_stmt]
      Completion::Types::NilType
    in [:dot2,]
      Completion::Types::InstanceType.new Range
    else
      STDERR.cooked{
        STDERR.puts
        STDERR.puts :NOMATCH
        STDERR.puts sexp.inspect
      }
      Completion::Types::NilType
    end
  end

  def self.type_of(fallback: Completion::Types::ObjectType)
    begin
      Completion::Types.type_from_object yield
    rescue
      fallback
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
    receiver ||= Completion::Types::SingletonType.new(Kernel)
    result = Completion::Types.rbs_method_response receiver, method.to_sym, args, kwargs, kwsplat, has_block
    result = Completion::Types::UnionType[result, Completion::Types::InstanceType.new(OBJECT_METHODS[method.to_sym])] if OBJECT_METHODS.has_key? method.to_sym
    result
  end

  def self.calculate_receiver(binding, parents, receiver)
    jumps = JumpPoints.new
    dig_targets = DigTarget.new(parents, receiver) do |types|
      return types
    end
    simulate_evaluate parents[0], Scope.from_binding(binding), jumps, dig_targets
    Completion::Types::NullType
  end
end
