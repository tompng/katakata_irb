require_relative 'nesting_parser'
require_relative 'type_simulator'
require 'rbs'
require 'rbs/cli'
require 'irb'

module KatakataIrb::Completor
  using KatakataIrb::TypeSimulator::LexerElemMatcher
  HIDDEN_METHODS = %w[Namespace TypeName] # defined by rbs, should be hidden
  singleton_class.attr_accessor :prev_analyze_result

  def self.setup
    completion_proc = ->(target, preposing = nil, postposing = nil) do
      code = "#{preposing}#{target}"
      irb_context = IRB.conf[:MAIN_CONTEXT]
      binding = irb_context.workspace.binding
      result = analyze code, binding
      KatakataIrb::Completor.prev_analyze_result = result
      candidates = case result
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
      in [:ivar, name, *_scope]
        # TODO: scope
        ivars = binding.eval('self').instance_variables rescue []
        cvars = (binding.eval('self').class_variables rescue nil) if name == '@'
        ivars | (cvars || [])
      in [:cvar, name, *_scope]
        # TODO: scope
        binding.eval('self').class_variables rescue []
      in [:gvar, name]
        global_variables
      in [:symbol, name]
        Symbol.all_symbols.map { _1.inspect[1..] }
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
      KatakataIrb.last_completion_error = e
      KatakataIrb.log_puts
      KatakataIrb.log_puts "#{e.inspect} stored to KatakataIrb.last_completion_error"
      KatakataIrb.log_puts
    end

    IRB::InputCompletor.singleton_class.prepend Module.new{
      def retrieve_completion_data(input, doc_namespace: false, **)
        return super unless doc_namespace
        name = input[/[a-zA-Z_0-9]+[!?=]?\z/]
        method_doc = -> type do
          type = type.types.find { _1.all_methods.include? name.to_sym }
          if type in KatakataIrb::Types::SingletonType
            "#{KatakataIrb::Types.class_name_of(type.module_or_class)}.#{name}"
          elsif type in KatakataIrb::Types::InstanceType
            "#{KatakataIrb::Types.class_name_of(type.klass)}##{name}"
          end
        end
        call_or_const_doc = -> type do
          if name =~ /\A[A-Z]/
            type = type.types.grep(KatakataIrb::Types::SingletonType).find { _1.module_or_class.const_defined?(name) }
            type.module_or_class == Object ? name : "#{KatakataIrb::Types.class_name_of(type.module_or_class)}::#{name}" if type
          else
            method_doc.call(type)
          end
        end

        case KatakataIrb::Completor.prev_analyze_result
        in [:call_or_const, type, _name, _self_call]
          call_or_const_doc.call type
        in [:const, type, _name]
          # when prev_analyze_result is const, current analyze result might be call
          call_or_const_doc.call type
        in [:gvar, _name]
          name
        in [:call, type, _name, _self_call]
          method_doc.call type
        in [:lvar_or_method, _name, scope]
          method_doc.call scope.self_type unless scope.local_variables.include?(name)
        else
        end
      end
    }
    setup_type_dialog
  end

  def self.setup_type_dialog
    type_dialog_proc = -> {
      return if just_cursor_moving && completion_journey_data
      cursor_pos_to_render, _result, pointer, autocomplete_dialog = context.last(4)
      return unless cursor_pos_to_render && autocomplete_dialog&.width && pointer.nil?
      receiver_type = (
        case KatakataIrb::Completor.prev_analyze_result
        in [:call_or_const, type, name, _self_call] if name.empty?
          type
        in [:call, type, name, _self_call] if name.empty?
          type
        else
          return
        end
      )
      return unless receiver_type
      types = type.types
      contents = types.filter_map do |type|
        case type
        when KatakataIrb::Types::InstanceType
          type.inspect_without_params
        else
          type.inspect
        end
      end.uniq
      return if contents.empty?

      width = contents.map { Reline::Unicode.calculate_width _1 }.max
      x = cursor_pos_to_render.x + autocomplete_dialog.width
      y = cursor_pos_to_render.y
      info = { pos: Reline::CursorPos.new(x, y), contents: contents, width: width, bg_color: 44, fg_color: 37 }
      Reline::DialogRenderInfo.new(**info.slice(*Reline::DialogRenderInfo.members))
    }
    Reline.add_dialog_proc(:show_type, type_dialog_proc, Reline::DEFAULT_DIALOG_CONTEXT)
  end

  def self.empty_binding()
    Kernel.binding
  end

  def self.analyze(code, binding = empty_binding)
    lvars_code = binding.local_variables.map do |name|
      "#{name}="
    end.join + "nil;\n"
    code = lvars_code + code
    tokens = RubyLex.ripper_lex_without_warning code
    tokens = KatakataIrb::NestingParser.interpolate_ripper_ignored_tokens code, tokens
    last_opens = KatakataIrb::NestingParser.open_tokens(tokens)
    closings = last_opens.map do |t|
      case t.tok
      when /\A%.?[<>]\z/
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
      when ':"', ":'", ':'
        t.tok[1]
      when '?'
        # ternary operator
        ' : value'
      when '|'
        # block args
        '|'
      else
        $/ + 'end'
      end
    end
    # remove error tokens
    tokens.pop while tokens&.last&.tok&.empty?

    case tokens.last
    in { event: :on_ignored_by_ripper, tok: '.' }
      suffix = 'method'
      name = ''
    in { dot: true }
      suffix = 'method'
      name = ''
    in { event: :on_symbeg }
      suffix = 'symbol'
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
    in { event: :on_gvar, tok: }
      return unless code.delete_suffix! tok
      suffix = '$gvar'
      name = tok
    in { event: :on_ivar, tok: }
      return unless code.delete_suffix! tok
      suffix = '@ivar'
      name = tok
    in { event: :on_cvar, tok: }
      return unless code.delete_suffix! tok
      suffix = '@@cvar'
      name = tok
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
    if target in [:@gvar,]
      return [:gvar, name]
    elsif target in [:@ivar,]
      return [:ivar, name] if icvar_available
    elsif target in [:@cvar,]
      return [:cvar, name] if icvar_available
    end
    return unless expression
    calculate_scope = -> { KatakataIrb::TypeSimulator.calculate_binding_scope binding, parents, expression }
    calculate_receiver = -> receiver { KatakataIrb::TypeSimulator.calculate_receiver binding, parents, receiver }

    if (target in [:@tstring_content,]) && (parents[-4] in [:command, [:@ident, 'require' | 'require_relative' => require_method,],])
      # `require 'target'`
      return [require_method.to_sym, name.rstrip]
    end
    if (target in [:@ident,]) && (expression in [:symbol,]) && (parents[-2] in [:args_add_block, Array => _args, [:symbol_literal, ^expression]])
      # `method(&:target)`
      receiver_ref = [:var_ref, [:@ident, '_1', [0, 0]]]
      block_statements = [receiver_ref]
      parents[-1] = parents[-2][-1] = [:brace_block, nil, block_statements]
      parents << block_statements
      return [:call, calculate_receiver.call(receiver_ref), name, false]
    end
    case expression
    in [:vcall | :var_ref, [:@ident,]]
      [:lvar_or_method, name, calculate_scope.call]
    in [:symbol, [:@ident | :@const | :@op | :@kw,]]
      [:symbol, name] unless name.empty?
    in [:var_ref | :const_ref, [:@const,]]
      # TODO
      [:const, KatakataIrb::Types::SingletonType.new(Object), name]
    in [:var_ref, [:@gvar,]]
      [:gvar, name]
    in [:var_ref, [:@ivar,]]
      [:ivar, name, calculate_scope.call.self_type] if icvar_available
    in [:var_ref, [:@cvar,]]
      [:cvar, name, calculate_scope.call.self_type] if icvar_available
    in [:call, receiver, [:@period,] | :'::' => dot, [:@ident | :@const,]]
      self_call = (receiver in [:var_ref, [:@kw, 'self',]])
      [dot == :'::' ? :call_or_const : :call, calculate_receiver.call(receiver), name, self_call]
    in [:call, receiver, [:@op, '&.',], [:@ident | :@const,]]
      self_call = (receiver in [:var_ref, [:@kw, 'self',]])
      [:call, calculate_receiver.call(receiver).nonnillable, name, self_call]
    in [:const_path_ref, receiver, [:@const,]]
      [:const, calculate_receiver.call(receiver), name]
    in [:top_const_ref, [:@const,]]
      [:const, KatakataIrb::Types::SingletonType.new(Object), name]
    in [:def,] | [:string_content,] | [:field | :var_field | :const_path_field,] | [:defs,] | [:rest_param,] | [:kwrest_param,] | [:blockarg,] | [[:@ident,],]
    in [Array,] # `xstring`, /regexp/
    else
      KatakataIrb.log_puts
      KatakataIrb.log_puts [:UNIMPLEMENTED_EXPRESSION, expression].inspect
      KatakataIrb.log_puts
      nil
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
