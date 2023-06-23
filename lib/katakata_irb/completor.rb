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
      in [:call_or_const, name, type, self_call]
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
        Symbol.all_symbols.map { _1.inspect[1..] }
      in [:call, name, type, self_call]
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
        in [:call_or_const, _name, type, _self_call]
          call_or_const_doc.call type
        in [:const, _name, type]
          # when prev_analyze_result is const, current analyze result might be call
          call_or_const_doc.call type
        in [:gvar, _name]
          name
        in [:call, _name, type, _self_call]
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
        in [:call_or_const, name, type, _self_call] if name.empty?
          type
        in [:call, name, type, _self_call] if name.empty?
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

  def self.completion_ast_targets(code, binding = empty_binding)
    lvars_code = binding.local_variables.map do |name|
      "#{name}="
    end.join + "nil;\n"
    code = lvars_code + code
    tokens = RubyLex.ripper_lex_without_warning code
    tokens = KatakataIrb::NestingParser.interpolate_ripper_ignored_tokens code, tokens
    last_opens = KatakataIrb::NestingParser.open_tokens(tokens)
    # remove error tokens
    tokens.pop while tokens&.last&.tok&.empty?

    tok = tokens.last&.tok
    case tokens.last
    in { event: :on_ignored_by_ripper | :on_op | :on_period, tok: '.' | '::' }
      mark = tok == '::' ? :IRB_COMPLETION_MARK : :irb_completion_mark
      tok = ''
    in { event: :on_symbeg }
      mark = :irb_completion_mark
      tok = ''
    in { event: :on_ident | :on_kw, tok: }
      mark = :irb_completion_mark
    in { event: :on_const, tok: }
      mark = :IRB_COMPLETION_MARK
    in { event: :on_tstring_content, tok: }
      mark = 'irb_completion_mark'
    in { event: :on_gvar, tok: }
      mark = :$irb_completion_mark
    in { event: :on_ivar, tok: }
      mark = :@irb_completion_mark
    in { event: :on_cvar, tok: }
      mark = :@@irb_completion_mark
    else
      return
    end

    code = code.delete_suffix(tok) unless tok.empty?
    last_opens = KatakataIrb::NestingParser.open_tokens(tokens)
    closing_code = KatakataIrb::NestingParser.closing_code(last_opens)

    begin
      verbose, $VERBOSE = $VERBOSE, nil
      ast = RubyVM::AbstractSyntaxTree.parse("#{code}#{mark}#{closing_code}")
    rescue SyntaxError
      return
    ensure
      $VERBOSE = verbose
    end

    matched_nodes = find_target_nodes(ast, mark)
    [matched_nodes, tok] if matched_nodes
  end

  def self.find_target_nodes(ast, mark)
    ast.children.each do |child|
      if mark == child
        return [ast]
      elsif child.is_a?(RubyVM::AbstractSyntaxTree::Node)
        result = find_target_nodes(child, mark)
        if result
          result.unshift ast
          return result
        end
      end
    end
    nil
  end

  def self.analyze(code, binding = empty_binding)
    (*parents, target), tok = completion_ast_targets code, binding
    return unless target

    calculate_scope = -> { return KatakataIrb::Scope.from_binding(binding); KatakataIrb::TypeSimulator.calculate_binding_scope binding, parents, target }
    calculate_receiver = -> receiver { return KatakataIrb::Types::INTEGER; KatakataIrb::TypeSimulator.calculate_receiver binding, parents, receiver }

    case target.type
    when :GVAR
      return [:gvar, tok, calculate_scope.call]
    when :IVAR
      return [:ivar, tok, calculate_scope.call]
    when :CVAR
      return [:cvar, tok, calculate_scope.call]
    when :LVAR, :VCALL
      return [:lvar_or_method, tok, calculate_scope.call]
    when :CONST
      return [:const_or_method, tok, calculate_scope.call]
    when :STR
      if parents[-3] in { type: :FCALL, children: [:require | :require_relative => method, { type: :LIST, children: [target, nil] }] }
        [method, tok.rstrip]
      end
    when :LIT
      return target.children[0].is_a?(Symbol) ? [:symbol, tok] : nil
    when :COLON2
      parent = target.children.first
      parent ? [:const_ref, tok, calculate_receiver.call(parent)] : [:const_or_method, tok, calculate_scope.call]
    when :COLON3
      [:top_const, tok]
    when :CALL
      [:call, tok, calculate_receiver.call(target.children.first), false]
    end
    # TODO: method(&:name)
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
