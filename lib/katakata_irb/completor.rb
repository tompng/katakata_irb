require_relative 'nesting_parser'
require_relative 'type_simulator'
require 'rbs'
require 'rbs/cli'
require 'irb'
require 'yarp'

module KatakataIrb::Completor
  using KatakataIrb::TypeSimulator::LexerElemMatcher
  HIDDEN_METHODS = %w[Namespace TypeName] # defined by rbs, should be hidden
  singleton_class.attr_accessor :prev_analyze_result

  def self.setup
    KatakataIrb::Types.preload_in_thread
    completion_proc = ->(target, preposing = nil, postposing = nil) do
      verbose, $VERBOSE = $VERBOSE, nil
      code = "#{preposing}#{target}"
      irb_context = IRB.conf[:MAIN_CONTEXT]
      binding = irb_context.workspace.binding
      result = analyze code, binding
      KatakataIrb::Completor.prev_analyze_result = result
      candidates = case result
      in [:require | :require_relative => method, name]
        if IRB.const_defined? :InputCompletor # IRB::VERSION <= 1.8.1
          path_completor = IRB::InputCompletor
        elsif IRB.const_defined? :RegexpCompletor # IRB::VERSION >= 1.8.2
          path_completor = IRB::RegexpCompletor.new
        end
        if !path_completor
          []
        elsif method == :require
          path_completor.retrieve_files_to_require_from_load_path
        else
          path_completor.retrieve_files_to_require_relative_from_current_dir
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
    rescue => e
      KatakataIrb.last_completion_error = e
      KatakataIrb.log_puts
      KatakataIrb.log_puts "#{e.inspect} stored to KatakataIrb.last_completion_error"
      KatakataIrb.log_puts
    ensure
      $VERBOSE = verbose
    end

    doc_namespace_proc = ->(input) do
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

    if IRB.const_defined? :InputCompletor # IRB::VERSION <= 1.8.1
      IRB::InputCompletor::CompletionProc.define_singleton_method :call do |*args|
        completion_proc.call(*args)
      end
      IRB::InputCompletor.singleton_class.prepend(
        Module.new do
          define_method :retrieve_completion_data do |input, doc_namespace: false, **kwargs|
            return super(input, doc_namespace: false, **kwargs) unless doc_namespace
            doc_namespace_proc.call input
          end
        end
      )
    elsif IRB.const_defined? :RegexpCompletor # IRB::VERSION >= 1.8.2
      IRB::RegexpCompletor.class_eval do
        define_method :completion_candidates do |preposing, target, postposing, bind:|
          completion_proc.call(target, preposing, postposing)
        end
        define_method :doc_namespace do |_preposing, matched, _postposing, bind:|
          doc_namespace_proc.call matched
        end
      end
    else
      puts 'Cannot activate katakata_irb'
    end

    setup_type_dialog
  end

  def self.type_dialog_content
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
    if KatakataIrb::Types.rbs_builder.nil? && !KatakataIrb::Types.rbs_load_error
      return [' Loading ', ' RBS... ']
    end
    types = receiver_type.types
    contents = types.filter_map do |type|
      case type
      when KatakataIrb::Types::InstanceType
        type.inspect_without_params
      else
        type.inspect
      end
    end.uniq
    contents if contents.any?
  end

  def self.setup_type_dialog
    type_dialog_proc = -> {
      return if just_cursor_moving && completion_journey_data
      cursor_pos_to_render, _result, pointer, autocomplete_dialog = context.last(4)
      return unless cursor_pos_to_render && autocomplete_dialog&.width && pointer.nil?
      contents = KatakataIrb::Completor.type_dialog_content
      return unless contents&.any?

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
    tokens = KatakataIrb::NestingParser.tokenize code
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
    full_code = code + suffix + closings.reverse.join
    ast = YARP.parse(full_code).value

    *parents, target_node = find_target ast, code.bytesize

    return unless target_node
    calculate_scope = -> { KatakataIrb::TypeSimulator.calculate_binding_scope binding, full_code, parents, target_node }
    calculate_receiver = -> receiver { KatakataIrb::TypeSimulator.calculate_receiver binding, full_code, parents, receiver }

    if target_node.is_a?(YARP::StringNode)
      args_node = parents[-1]
      call_node = parents[-2]
      return unless args_node.is_a?(YARP::ArgumentsNode) && args_node.arguments.size == 1
      return unless call_node.is_a?(YARP::CallNode) && call_node.receiver.nil? && (call_node.message in 'require' | 'require_relative')
      return [call_node.message.to_sym, name.rstrip]
    end

    # if (target in [:@ident,]) && (expression in [:symbol,]) && (parents[-2] in [:args_add_block, Array => _args, [:symbol_literal, ^expression]])
    #   # `method(&:target)`
    #   receiver_ref = [:var_ref, [:@ident, '_1', [0, 0]]]
    #   block_statements = [receiver_ref]
    #   parents[-1] = parents[-2][-1] = [:brace_block, nil, block_statements]
    #   parents << block_statements
    #   return [:call, calculate_receiver.call(receiver_ref), name, false]
    # end
    case target_node
    when YARP::SymbolNode
      # TODO: method(&:target)
      [:symbol, name] unless name.empty?
    when YARP::CallNode
      return [:lvar_or_method, name, calculate_scope.call] if target_node.receiver.nil?
      self_call = target_node.receiver.is_a? YARP::SelfNode
      op = target_node.operator
      receiver_type = calculate_receiver.call target_node.receiver
      receiver_type = receiver_type.nonnillable if op == '&.'
      [op == :'::' ? :call_or_const : :call, receiver_type, name, self_call]
    when YARP::LocalVariableReadNode
      [:lvar_or_method, name, calculate_scope.call]
    when YARP::ConstantReadNode
      # TODO: scope
      [:const, KatakataIrb::Types::SingletonType.new(Object), name]
    when YARP::GlobalVariableReadNode
      [:gvar, name]
    when YARP::InstanceVariableReadNode
      [:ivar, name, calculate_scope.call.self_type]
    when YARP::ClassVariableReadNode
      [:cvar, name, calculate_scope.call.self_type]
    when YARP::ConstantPathNode
      if target_node.receiver.nil?
        [:const, KatakataIrb::Types::SingletonType.new(Object), name]
      else
        [:const, calculate_receiver.call(target_node.receiver), name]
      end
    when YARP::DefNode
      # do nothing
    else
      KatakataIrb.log_puts
      KatakataIrb.log_puts [:UNIMPLEMENTED_EXPRESSION, target_node].inspect
      KatakataIrb.log_puts
      nil
    end
  end

  def self.find_target(node, position)
    location = (
      case node
      when YARP::CallNode
        node.message_loc
      when YARP::SymbolNode
        node.value_loc
      when YARP::StringNode
        node.content_loc
      when YARP::Node
        node.location
      end
    )
    return [node] if location&.start_offset == position

    node.child_nodes.each do |n|
      next unless n.is_a? YARP::Node
      match = find_target(n, position)
      next unless match
      match.unshift node
      return match
    end
    nil
  end
end
