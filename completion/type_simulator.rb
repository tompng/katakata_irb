require_relative 'types'
require 'ripper'
module Completion; end
module Completion::TypeSimulator

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
        when :lvar
          Completion::TypeSimulator.type_of { @binding.eval name.to_s }
        end
      )
    end

    def self.type_by_name(name)
      name.start_with?('@@') ? :cvar : name.start_with?('@') ? :ivar : :lvar
    end
  end

  class Scope
    def initialize(parent, trace_cvar: true, trace_ivar: true, trace_lvar: true)
      @table = {}
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
      @table[name] || (@parent[name] if trace? name)
    end

    def set(name, types, conditional: false)
      if trace?(name) && @parent.mutable? && @parent.has?(name)
        @parent.set(name, types, conditional:)
      elsif conditional
        @table[name] = (self[name] || []) | types
      else
        @table[name] = types
      end
    end

    alias []= set

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

  def self.simulate_evaluate(sexp, binding, lvar_available, icvar_available)
    case sexp
    in [:def,]
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
    in [:array,]
      [Array]
    in [:hash,]
      [Hash]
    in [:paren, statements]
      simulate_evaluate statements.last, binding, lvar_available, icvar_available
    in [:const_path_ref, receiver, [:@const, name,]]
      simulate_evaluate(receiver, binding, lvar_available, icvar_available).flat_map do |k|
        (k in { class: klass }) ? type_of { klass.const_get name } : []
      end
    in [:var_ref, [:@kw, name,]]
      klass = { 'true' => TrueClass, 'false' => FalseClass, 'nil' => NilClass }[name]
      [*klass]
    in [:var_ref, [:@const, name,]]
      type_of { Object.const_get name }
    in [:var_ref, [:@ivar | :@cvar, name,]]
      icvar_available ? type_of { binding.eval name } : []
    in [:var_ref, [:@gvar, name,]]
      type_of { binding.eval name }
    in [:var_ref, [:@ident, name,]]
      lvar_available ? type_of { binding.eval name } : []
    in [:aref, receiver, args]
      receiver_type = simulate_evaluate receiver, binding, lvar_available, icvar_available if receiver
      args, kwargs, kwsplat, block = retrieve_method_args args
      args_type = args.map { simulate_evaluate _1, binding, lvar_available, icvar_available if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, binding, lvar_available, icvar_available }
      simulate_call receiver_type, :[], args_type, kwargs_type, kwsplat, block
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      receiver, method, args, kwargs, kwsplat, block = retrieve_method_call sexp
      receiver_type = simulate_evaluate receiver, binding, lvar_available, icvar_available if receiver
      args_type = args.map { simulate_evaluate _1, binding, lvar_available, icvar_available if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, binding, lvar_available, icvar_available }
      simulate_call receiver_type, method, args_type, kwargs_type, kwsplat, block
    in [:binary, a, Symbol => op, b]
      simulate_call simulate_evaluate(a, binding, lvar_available, icvar_available), op, [simulate_evaluate(b, binding, lvar_available, icvar_available)], {}, false, false
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, binding, lvar_available, icvar_available), op, [], {}, false, false
    in [:lambda,]
      [Proc]
    in [:assign | :massign, _target, value]
      simulate_evaluate(value, binding, lvar_available, icvar_available)
    in [:mrhs_new_from_args,]
      [Array]
    in [:if | :unless | :while | :until | :case | :begin | :for | :class | :sclass | :module | :ifop | :rescue_mod,]
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
      [nil, method, [], {}, false, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', :call] # a.()
      [receiver, :call, [], {}, false, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const | :@kw | :@op, method,]] # a.hoge
      [receiver, method, [], {}, false, false]
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
    in [:method_add_block, call, _block]
      receiver, method, args, kwargs, kwsplat = retrieve_method_call call
      [receiver, method, args, kwargs, kwsplat, true]
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
      [[], kwargs, kwsplat, false]
    in [:args_add_star, *args, [:bare_assoc_hash,] => kwargs]
      args, = retrieve_method_args [:args_add_star, *args]
      _, kwargs, kwsplat = retrieve_method_args kwargs
      [args, kwargs, kwsplat, false]
    in [:args_add_star, pre_args, star_arg, *post_args]
      pre_args, = retrieve_method_args pre_args if pre_args in [:args_add_star,]
      args = [*pre_args, nil, *post_args]
      [args, {}, false, false]
    in [:arg_paren, args]
      args ? retrieve_method_args(args) : [[], {}, false, false]
    else
      [[], {}, false, false]
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
end
