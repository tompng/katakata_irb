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

  def self.rbs_method_response(klass, method_name, args_types, kwargs_types, has_block)
    singleton = (klass in { class: klass })
    return [klass] if singleton && method_name == :new
    return [{ class: klass }] if !singleton && method_name == :class
    type_name = RBS::TypeName(klass.name).absolute!
    definition = (singleton ? rbs_builder.build_singleton(type_name) : rbs_builder.build_instance(type_name)) rescue nil
    return [] unless definition
    method = definition.methods[method_name]
    return [] unless method
    has_splat = !args_types.all?
    method_types_with_score = method.method_types.map do |method_type|
      match = 0
      match += 10 if !!method_type.block == has_block
      positionals = method_type.type.required_positionals
      if has_splat
        match += 5 if args_types.size <= positionals.size
      elsif args_types.size == positionals.size
        match += 10
      end
      [method_type, match]
    end
    max_score = method_types_with_score.map(&:last).max
    method_types_with_score.select { _2 == max_score }.map(&:first).flat_map do
      class_from_rbs_type _1.type.return_type, klass
    end
  end

  def self.class_from_rbs_type(return_type, self_class)
    case return_type
    when RBS::Types::Bases::Self
      return self_class
    when RBS::Types::Literal
      return return_type.literal.class
    when RBS::Types::Bases::Bool
      return [TrueClass, FalseClass]
    when RBS::Types::Variable
      return [Object, NilClass]
    when RBS::Types::Bases::Any
      return [Object, NilClass]
    when RBS::Types::Optional
      return class_from_rbs_type return_type.type, self_class
    end
    name = return_type.name
    return Object.const_get name.name if name.kind == :class
    case name.name
    when :int
      Integer
    when :float
      Float
    when :string
      String
    when :nil
      NilClass
    when :true
      TrueClass
    when :false
      FalseClass
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

  def self.patch_to_completor
    completion_proc = ->(target, preposing = nil, postposing = nil) do
      code = "#{preposing}#{target}"
      irb_context = IRB.conf[:MAIN_CONTEXT]
      binding = irb_context.workspace.binding
      lvars_code = RubyLex.generate_local_variables_assign_code binding.local_variables
      tokens = RubyLex.ripper_lex_without_warning lvars_code + code, context: irb_context
      suffix = code.end_with?('.') && tokens.last&.tok != '.' ? '.' : ''
      result = analyze(tokens, binding, suffix:)
      candidates = case result
      in [:require | :require_relative => method, name]
        if method == :require
          IRB::InputCompletor.retrieve_files_to_require_from_load_path
        else
          IRB::InputCompletor.retrieve_files_to_require_relative_from_current_dir
        end
      in [:const, classes, name]
        classes.flat_map do |k|
          (k in { class: klass }) ? klass.constants : []
        end
      in [:ivar, name]
        ivars = binding.eval('self').instance_variables rescue []
        cvars = (binding.eval('self').class_variables rescue nil) if name == '@'
        ivars | (cvars || [])
      in [:cvar, name]
        binding.eval('self').class_variables rescue []
      in [:gvar, name]
        global_variables
      in [:symbol, name]
        Symbol.all_symbols.reject { _1.match? '_trex_completion_' }
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
      candidates.map(&:to_s).select { _1.start_with? name }.uniq.sort.map do
        target + _1[name.size..]
      end
    end
    IRB::InputCompletor::CompletionProc.define_singleton_method :call do |*args|
      completion_proc.call(*args)
    end
  end

  def self.analyze(tokens, binding = Kernel.binding, suffix: '')
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
      when '"', "'"
        t.tok
      else
        'end'
      end
    end
    icvar_available = !last_opens.any? {|t,| t in { event: :on_kw, tok: 'class' | 'module' } }
    lvar_available = !last_opens.any? {|t,| t in { event: :on_kw, tok: 'class' | 'module' | 'def' } }
    alphabet = ('a'..'z').to_a
    mark = "_trex_completion_#{8.times.map { alphabet.sample }.join}x"
    code = tokens.map(&:tok).join + suffix + mark + $/ + closing_heredocs.reverse.join($/) + $/ + closings.reverse.join($/)
    sexp = Ripper.sexp code
    *parents, expression, target, _token = find_pattern sexp, mark
    return unless target in [type, String => name_with_mark, [Integer, Integer]]
    name = name_with_mark.sub mark, ''
    if target in [:@ivar,]
      return [:ivar, name] if icvar_available
    elsif target in [:@cvar,]
      return [:cvar, name] if icvar_available
    end
    return unless expression
    if (target in [:@tstring_content,]) && (parents[-4] in [:command, [:@ident, 'require' | 'require_relative' => require_method,],])
      return [require_method.to_sym, name.rstrip]
    end
    case expression
    in [:vcall | :var_ref, [:@ident,]]
      if lvar_available
        [:lvar_or_method, name]
      else
        [:call, [{ class: Kernel }], name]
      end
    in [:symbol, [:@ident | :@const | :@op | :@kw,]]
      [:symbol, name]
    in [:var_ref | :const_ref, [:@const,]]
      [:const, [{ class: Object }], name]
    in [:var_ref, [:@gvar,]]
      [:gvar, name]
    in [:var_ref, [:@ivar,]]
      [:ivar, name] if icvar_available
    in [:var_ref, [:@cvar,]]
      [:cvar, name] if icvar_available
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const, ^name_with_mark,]]
      [:call, simulate_evaluate(receiver, binding, lvar_available, icvar_available), name]
    in [:const_path_ref, receiver, [:@const,]]
      [:const, simulate_evaluate(receiver, binding, lvar_available, icvar_available), name]
    in [:def,] | [:string_content,] | [:var_field,]
    else
      STDERR.cooked{
        10.times { STDERR.puts }
        STDERR.puts [:ERROR, expression].inspect
        10.times { STDERR.puts }
      }
    end
  end

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
      args, kwargs, block = retrieve_method_args args
      simulate_call receiver_type, :[], args, kwargs, block
    in [:call | :vcall | :command | :command_call | :method_add_arg | :method_add_block,]
      receiver, method, args, kwargs, block = retrieve_method_call sexp
      receiver_type = simulate_evaluate receiver, binding, lvar_available, icvar_available if receiver
      args_type = args&.map { simulate_evaluate _1, binding, lvar_available, icvar_available if _1 }
      kwargs_type = kwargs&.transform_values { simulate_evaluate _1, binding, lvar_available, icvar_available }
      simulate_call receiver_type, method, args_type, kwargs_type, !!block
    in [:binary, a, Symbol => op, b]
      simulate_call simulate_evaluate(a, binding, lvar_available, icvar_available), op, [simulate_evaluate(b, binding, lvar_available, icvar_available)], {}, false
    in [:unary, op, receiver]
      simulate_call simulate_evaluate(receiver, binding, lvar_available, icvar_available), op, [], {}, false
    in [:lambda,]
      [Proc]
    in [:assign, target, value]
      simulate_evaluate(value, binding, lvar_available, icvar_available)
    in [:if | :unless | :while | :until | :case | :begin | :for | :class | :module | :ifop | :rescue_mod,]
      []
    in [:void_stmt]
      [NilClass]
    else
      STDERR.cooked{
        10.times{puts}
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
      [nil, method, [], {}, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', :call] # a.()
      [receiver, :call, [], {}, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::', [:@ident | :@const | :@kw | :@op, method,]] # a.hoge
      [receiver, method, [], {}, false]
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
      receiver, method, args, kwargs = retrieve_method_call(call)
      [receiver, method, args, kwargs, true]
    end
  end

  def self.retrieve_method_args(sexp)
    case sexp
    in [:args_add_block, [:args_add_star,] => args, block_arg]
      args, = retrieve_method_args args
      [args, {}, block_arg]
    in [:args_add_block, [*args, [:bare_assoc_hash,] => kwargs], block_arg]
      args, = retrieve_method_args args
      _, kwargs, = retrieve_method_args kwargs
      [args, kwargs, block_arg]
    in [:args_add_block, [*args], block_arg]
      [args, {}, block_arg]
    in [:bare_assoc_hash, kws]
      kwargs = {}
      kws.each do |kw|
        if kw in [:assoc_new, [:@label, label,], value]
          key = label.delete ':'
          kwargs[key] = value || [:var_ref, [key =~ /\A[A-Z]/ ? :@const : :@ident, key, [0, 0]]]
        end
      end
      [[], kwargs, false]
    in [:args_add_star, *args, [:bare_assoc_hash,] => kwargs]
      args, = retrieve_method_args [:args_add_star, *args]
      _, kwargs, = retrieve_method_args kwargs
      [args, kwargs, false]
    in [:args_add_star, pre_args, star_arg, *post_args]
      pre_args, = retrieve_method_args pre_args if pre_args in [:args_add_star,]
      args = [*pre_args, nil, *post_args]
      [args, {}, false]
    in [:arg_paren, args]
      args ? retrieve_method_args(args) : [[], {}, false]
    else
      [[], {}, false]
    end
  end

  def self.simulate_call(receiver, method, args, kwargs, has_block)
    receiver ||= [{ class: Kernel }]
    result = receiver.flat_map do |klass|
      rbs_method_response klass, method.to_sym, args, kwargs, has_block
    end.uniq
    result |= [OBJECT_METHODS[method.to_sym]] if OBJECT_METHODS.has_key? method.to_sym
    result.empty? ? [Object, NilClass] : result
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
  RUBY
  tokens = RubyLex.ripper_lex_without_warning(code)
  p Completion.analyze tokens
end
