require_relative './trex'
require 'rbs'
require 'rbs/cli'
require 'irb'

module Completion
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

  def self.rbs_builder
    @rbs_builder ||= RBS::DefinitionBuilder.new(
      env: RBS::Environment.from_loader(RBS::CLI::LibraryOptions.new.loader).resolve_type_names
    )
  end

  def self.method_response(klass, method)
    singleton = false
    singleton = true if klass in { class: klass }
    return [klass] if singleton && method == :new
    return [{ class: klass }] if !singleton && method == :class
    type_name = RBS::TypeName(klass.name).absolute!
    definition = (singleton ? rbs_builder.build_singleton(type_name) : rbs_builder.build_instance(type_name)) rescue nil
    return [] unless definition
    method = definition.methods[method]
    return [] unless method
    names = method.method_types.filter_map { |method_type| method_type.type.return_type.name.name rescue nil }.uniq
    names.filter_map { Object.const_get _1 rescue nil }
  rescue => e
    p ERROR: klass
    STDOUT.cooked{puts e.backtrace}
    exit
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

  def self.patch_to_completor
    completion_proc = ->(target, preposing = nil, postposing = nil) do
      code = "#{preposing}#{target}"
      tokens = RubyLex.ripper_lex_without_warning code
      binding = IRB.conf[:MAIN_CONTEXT].workspace.binding
      suffix = code.end_with?('.') && tokens.last&.tok != '.' ? '.' : ''
      result = analyze tokens, binding, suffix
      candidates = case result
      in [:require, method, lib]
        ['irb', 'reline']
      in [:const, classes, name]
        classes.flat_map do |k|
          (k in { class: klass }) ? klass.constants : []
        end
      in [:gvar, name]
        global_variables
      in [:symbol, name]
        Symbol.all_symbols
      in [:call, classes, name]
        classes.flat_map do |k|
          if k in { class: klass }
            klass.methods
          else
            k.instance_methods
          end
        end
      in [:lvar_or_method, name]
        Kernel.methods | binding.local_variables
      else
        []
      end
      candidates.select { _1.start_with? name }.uniq.sort.map do
        target + _1.to_s[name.size..]
      end
    end
    IRB::InputCompletor.const_set :CompletionProc, completion_proc
  end

  def self.analyze(tokens, binding = Kernel.binding, suffix = '')
    return if tokens.last&.tok =~ /(\?|\!)\z/
    last_opens, unclosed_heredocs = TRex.parse(tokens){ }
    closing_heredocs = unclosed_heredocs.map {|t|
      t.tok.match(/\A<<(?:"(?<s>.+)"|'(?<s>.+)'|(?<s>.+))/)[:s]
    }
    closings = last_opens.map do |t,|
      case t.tok
      when /\A%.[<>]\z/
        '>'
      when '{', /\A%.[{}]\z/
        '}'
      when '(', /\A%.[()]\z/
        ')'
      when '[', /\A%.[\[\]]\z/
        ']'
      when /\A%.?(.)\z/
        $1
      else
        'end'
      end
    end
    ivar_cvar_available = !last_opens.any? {|t,| t in { event: :on_kw, tok: 'class' | 'module' } }
    lvar_available = !last_opens.any? {|t,| t in { event: :on_kw, tok: 'class' | 'module' | 'def' } }
    alphabet = ('a'..'z').to_a
    mark = "_completion_#{8.times.map { alphabet.sample }.join}x"
    code = tokens.map(&:tok).join + suffix + mark + $/ + closing_heredocs.reverse.join($/) + $/ + closings.reverse.join($/)
    sexp = Ripper.sexp code
    *, expression, target, _token = find_pattern sexp, mark
    return unless expression && (target in [type, String => name_with_mark, [Integer, Integer]])
    name = name_with_mark.sub mark, ''
    case expression
    in [:vcall, [:@ident,]]
      if lvar_available
        [:lvar_or_method, name]
      else
        [:call, [{ class: Kernel }], name]
      end
    in [:symbol, [:@ident,]]
      [:symbol, name]
    in [:var_ref | :const_ref, [:@const,]]
      [:const, [{ class: Object }], name]
    in [:var_ref, [:@gvar,]]
      [:gvar, name]
    in [:var_ref, [:@ivar,]]
      [:ivar, name] if ivar_cvar_available
    in [:var_ref, [:@cvar,]]
      [:cvar, name] if ivar_cvar_available
    in [:call, receiver, [:@period,] | :'::', [:@ident | :@const, ^name_with_mark,]]
      [:call, simulate_evaluate(receiver), name]
    in [:const_path_ref, receiver, [:@const,]]
      [:const, simulate_evaluate(receiver), name]
    else
      STDOUT.cooked{
        10.times { puts }
        p [:ERROR, expression]
      }
      binding.irb
      exit
    end
  end

  def self.simulate_evaluate(sexp)
    result = case sexp
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
      simulate_evaluate statements.last
    in [:const_path_ref, receiver, [:@const, name,]]
      simulate_evaluate(receiver).filter_map do |k|
        begin
          if k in { class: klass }
            value = klass.const_get name
            value.is_a?(Module) ? { class: value } : value.class
          end
        rescue
        end
      end
    in [:var_ref, [:@kw, name,]]
      klass = { 'true' => TrueClass, 'false' => FalseClass, 'nil' => NilClass }[name]
      [*klass]
    in [:var_ref, [:@const, name,]]
      begin
        value = Object.const_get name
        value.is_a?(Module) ? [{ class: value }] : [value.class]
      rescue
        []
      end
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      receiver, method, args, kwargs, block = retrieve_method_call sexp
      receiver_type = simulate_evaluate receiver if receiver
      args_type = args&.map { simulate_evaluate _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1 }
      simulate_call receiver_type, method, args_type, kwargs_type, block
    in [:binary, a, Symbol => op, b]
      simulate_call simulate_evaluate(a), op, [simulate_evaluate(b)], {}, false
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver), op, [], {}, false
    end
    result
  end

  def self.retrieve_method_call(sexp)
    case sexp
    in [:fcall | :vcall, [:@ident | :@const | :@kw | :@op, method,]] # hoge
      [nil, method, [], {}, false]
    in [:call, receiver, [:@period,] | :'::', [:@ident | :@const | :@kw | :@op, method,]] # a.hoge
      [receiver, method, [], {}, false]
    in [:command, [:@ident | :@const | :@kw | :@op, method,], args] # hoge 1, 2
      args, kwargs, block = retrieve_method_args args
      [nil, method, args, kwargs, block]
    in [:command_call, receiver, [:@period,] | :'::', [:@ident | :@const | :@kw | :@op, method,], args] # a.hoge 1; a.hoge 1, 2;
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block]
    in [:method_add_arg, call, args]
      receiver, method = retrieve_method_call call
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block]
    in [:method_add_block, call, block]
      receiver, method, args, kwargs = retrieve_method_call(call)
      [receiver, method, args, kwargs, true]
    end
  end

  def self.retrieve_method_args(sexp)
    # case sexp
    # in [:args_add_block, [:args_add_star]]
    # in [:arg_paren, args]
    # end
    # unimplemented
    [[], {}, false]
  end

  def self.simulate_call(receiver, method, _args, _kwargs, _has_block)
    receiver ||= [{ class: Kernel }]
    result = receiver.flat_map do |klass|
      method_response klass, method.to_sym
    end.uniq
    result |= [OBJECT_METHODS[method.to_sym]] if OBJECT_METHODS.has_key? method.to_sym
    result
  end

  def self.find_pattern(sexp, pattern, stack = [sexp])
    return unless sexp.is_a? Array
    sexp.each do |child|
      if child.is_a?(String) && child.include?(pattern)
        stack << child
        return stack
      else
        stack << child
        result = find_pattern(child, pattern, stack)
        return result if result
        stack.pop
      end
    end
    nil
  end

end

if $0 == __FILE__
  code = <<~'RUBY'.chomp
    a = 1
    def geso()
      p 1
      10.times do |i|
        ([1, 2, ((3+(i.times.map{}.size+4)*5.to_i).itself
        hoge
        %[]
        %w[]; %W[]; %Q[]; %s[]; %i[]; %I[]+A::DATA
        .times do
        end[0].a(1).b{2}.c[3].d{4}[5].e
        123.to_f.hoge
        %[].aa
        '$hello'.to_s.size.times.map.to_a.hoge.to_a.hoge
        hoge.to_i.hoge
  RUBY
  tokens = RubyLex.ripper_lex_without_warning(code)
  p Completion.analyze tokens
end
