require_relative 'nesting_parser'
require_relative 'type_simulator'
require 'rbs'
require 'rbs/cli'
require 'irb'

module KatakataIrb::Completor
  using KatakataIrb::TypeSimulator::LexerElemMatcher

  HIDDEN_METHODS = %w[Namespace TypeName] # defined by rbs, should be hidden

  def self.setup
    completion_proc = ->(target, preposing = nil, postposing = nil) do
      code = "#{preposing}#{target}"
      irb_context = IRB.conf[:MAIN_CONTEXT]
      binding = irb_context.workspace.binding
      candidates = case analyze code, binding
      in [:require | :require_relative => method, name]
        if method == :require
          IRB::InputCompletor.retrieve_files_to_require_from_load_path
        else
          IRB::InputCompletor.retrieve_files_to_require_relative_from_current_dir
        end
      in [:call_or_const, type, name, self_call]
        ((self_call ? type.all_methods: type.methods).map(&:to_s) - HIDDEN_METHODS) | type.constants
      in [:const, type, name]
        type.constants
      in [:ivar, name, _scope]
        # TODO: scope
        ivars = binding.eval('self').instance_variables rescue []
        cvars = (binding.eval('self').class_variables rescue nil) if name == '@'
        ivars | (cvars || [])
      in [:cvar, name, _scope]
        # TODO: scope
        binding.eval('self').class_variables rescue []
      in [:gvar, name]
        global_variables
      in [:symbol, name]
        Symbol.all_symbols
      in [:call, type, name, self_call]
        (self_call ? type.all_methods : type.methods).map(&:to_s) - HIDDEN_METHODS
      in [:lvar_or_method, name, scope]
        scope.self_type.all_methods.map(&:to_s) | scope.local_variables
      else
        []
      end
      all_symbols_pattern = /\A[ -\/:-@\[-`\{-~]*\z/
      candidates.map(&:to_s).select { !_1.match?(all_symbols_pattern) && _1.start_with?(name) }.uniq.sort.map do
        target + _1[name.size..]
      end
    end
    IRB::InputCompletor::CompletionProc.define_singleton_method :call do |*args|
      completion_proc.call(*args)
    rescue => e
      $error = e
      KatakataIrb.log_puts
      KatakataIrb.log_puts "#{e.inspect} stored to $error"
      KatakataIrb.log_puts
    end
  end

  def self.analyze(code, binding = Kernel.binding)
    lvars_code = binding.local_variables.map do |name|
      "#{name}="
    end.join + "nil;\n"
    code = lvars_code + code
    tokens = RubyLex.ripper_lex_without_warning code
    tokens = KatakataIrb::NestingParser.interpolate_ripper_ignored_tokens code, tokens
    last_opens = KatakataIrb::NestingParser.parse(tokens)
    closings = last_opens.map do |t|
      case t.tok
      when /\A%.[<>]\z/
        $/ + '>'
      when '{', '#{', /\A%.?[{}]\z/
        $/ + '}'
      when '(', /\A%.?[()]\z/
        # do not insert \n before closing paren. workaround to avoid syntax error of "a in ^(b\n)"
        ')'
      when '[', /\A%.?[\[\]]\z/
        $/ + ']'
      when /\A%.?(.)\z/
        $1
      when '"', "'", '/', '`'
        t.tok
      when /\A<<[~-]?(?:"(?<s>.+)"|'(?<s>.+)'|(?<s>.+))/
        $/ + ($1 || $2 || $3) + $/
      else
        $/ + 'end'
      end
    end

    return if code =~ /[!?]\z/
    case tokens.last
    in { event: :on_ignored_by_ripper, tok: '.' }
      suffix = 'method'
      name = ''
    in { dot: true }
      suffix = 'method'
      name = ''
    in { event: :on_ident | :on_kw, tok: }
      return unless code.delete_suffix! tok
      suffix = 'method'
      name = tok
    in { event: :on_const, tok: }
      return unless code.delete_suffix! tok
      suffix = 'Const'
      name = tok
    in { event: :on_tstring_content, tok: }
      return unless code.delete_suffix! tok
      suffix = 'string'
      name = tok.rstrip
    else
      return
    end

    sexp = Ripper.sexp code + suffix + closings.reverse.join
    lines = code.lines
    line_no = lines.size
    col = lines.last.bytesize
    if lines.last.end_with? "\n"
      line_no += 1
      col = 0
    end

    if sexp in [:program, [_lvars_exp, *rest_statements]]
      sexp = [:program, rest_statements]
    end

    *parents, expression, target = find_target sexp, line_no, col
    in_class_module = parents&.any? { _1 in [:class | :module,] }
    icvar_available = !in_class_module
    return unless target in [_type, String, [Integer, Integer]]
    if target in [:@ivar,]
      return [:ivar, name] if icvar_available
    elsif target in [:@cvar,]
      return [:cvar, name] if icvar_available
    end
    return unless expression
    if (target in [:@tstring_content,]) && (parents[-4] in [:command, [:@ident, 'require' | 'require_relative' => require_method,],])
      return [require_method.to_sym, name.rstrip]
    end
    calculate_scope = -> { KatakataIrb::TypeSimulator.calculate_binding_scope binding, parents, expression }
    calculate_receiver = -> receiver { KatakataIrb::TypeSimulator.calculate_receiver binding, parents, receiver }
    case expression
    in [:vcall | :var_ref, [:@ident,]]
      [:lvar_or_method, name, calculate_scope.call]
    in [:symbol, [:@ident | :@const | :@op | :@kw,]]
      [:symbol, name]
    in [:var_ref | :const_ref, [:@const,]]
      # TODO
      [:const, KatakataIrb::Types::SingletonType.new(Object), name]
    in [:var_ref, [:@gvar,]]
      [:gvar, name]
    in [:var_ref, [:@ivar,]]
      [:ivar, name, calculate_scope.call.self_type] if icvar_available
    in [:var_ref, [:@cvar,]]
      [:cvar, name, calculate_scope.call.self_type] if icvar_available
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, [:@ident | :@const,]]
      self_call = (receiver in [:var_ref, [:@kw, 'self',]])
      [dot == :'::' ? :call_or_const : :call, calculate_receiver.call(receiver), name, self_call]
    in [:const_path_ref, receiver, [:@const,]]
      [:const, calculate_receiver.call(receiver), name]
    in [:top_const_ref, [:@const,]]
      [:const, KatakataIrb::Types::SingletonType.new(Object), name]
    in [:def,] | [:string_content,] | [:var_field,] | [:defs,] | [:rest_param,] | [:kwrest_param,] | [:blockarg,] | [[:@ident,],]
    in [Array,] # `xstring`, /regexp/
    else
      KatakataIrb.log_puts
      KatakataIrb.log_puts [:NEW_EXPRESSION, expression].inspect
      KatakataIrb.log_puts
    end
  end

  def self.find_target(sexp, line, col, stack = [sexp])
    return unless sexp.is_a? Array
    sexp.each do |child|
      case child
      in [Symbol, String, [Integer => l, Integer => c]]
        if l == line && c == col
          stack << child
          return stack
        end
      else
        stack << child
        result = find_target(child, line, col, stack)
        return result if result
        stack.pop
      end
    end
    nil
  end
end
