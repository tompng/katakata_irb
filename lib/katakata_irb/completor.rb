# frozen_string_literal: true

require_relative 'type_analyzer'
require 'irb'
require 'prism'

module KatakataIrb::Completor
  HIDDEN_METHODS = %w[Namespace TypeName] # defined by rbs, should be hidden
  singleton_class.attr_accessor :prev_analyze_result

  def self.candidates_from_result(result)
    candidates = case result
    in [:require | :require_relative => method, name]
      if IRB.const_defined? :RegexpCompletor # IRB::VERSION >= 1.8.2
        path_completor = IRB::RegexpCompletor.new
      elsif IRB.const_defined? :InputCompletor # IRB::VERSION <= 1.8.1
        path_completor = IRB::InputCompletor
      end
      if !path_completor
        []
      elsif method == :require
        path_completor.retrieve_files_to_require_from_load_path
      else
        path_completor.retrieve_files_to_require_relative_from_current_dir
      end
    in [:call_or_const, type, name, self_call]
      ((self_call ? type.all_methods : type.methods).map(&:to_s) - HIDDEN_METHODS) | type.constants
    in [:const, type, name, scope]
      if type
        scope_constants = type.types.flat_map do |t|
          scope.table_module_constants(t.module_or_class) if t.is_a?(KatakataIrb::Types::SingletonType)
        end
        (scope_constants.compact | type.constants.map(&:to_s)).sort
      else
        scope.constants.sort
      end
    in [:ivar, name, scope]
      ivars = scope.instance_variables.sort
      name == '@' ? ivars + scope.class_variables.sort : ivars
    in [:cvar, name, scope]
      scope.class_variables
    in [:gvar, name, scope]
      scope.global_variables
    in [:symbol, name]
      Symbol.all_symbols.map { _1.inspect[1..] }
    in [:call, type, name, self_call]
      (self_call ? type.all_methods : type.methods).map(&:to_s) - HIDDEN_METHODS
    in [:lvar_or_method, name, scope]
      scope.self_type.all_methods.map(&:to_s) | scope.local_variables
    else
      []
    end
    [name || '', candidates]
  end

  def self.setup
    KatakataIrb::Types.preload_in_thread
    completion_proc = ->(preposing, target, _postposing, bind:) do
      verbose, $VERBOSE = $VERBOSE, nil
      code = "#{preposing}#{target}"
      result = analyze code, bind
      KatakataIrb::Completor.prev_analyze_result = result
      name, candidates = candidates_from_result(result).dup

      all_symbols_pattern = /\A[ -\/:-@\[-`\{-~]*\z/
      candidates.map(&:to_s).select { !_1.match?(all_symbols_pattern) && _1.start_with?(name) }.uniq.sort.map do
        target + _1[name.size..]
      end
    rescue SyntaxError, StandardError => e
      KatakataIrb.last_completion_error = e
      KatakataIrb.log_puts
      KatakataIrb.log_puts "#{e.inspect} stored to KatakataIrb.last_completion_error"
      KatakataIrb.log_puts
    ensure
      $VERBOSE = verbose
    end

    doc_namespace_proc = -> input do
      name = input[/[a-zA-Z_0-9]*[!?=]?\z/]
      method_doc = -> type do
        type = type.types.find { _1.all_methods.include? name.to_sym }
        if type.is_a? KatakataIrb::Types::SingletonType
          "#{KatakataIrb::Types.class_name_of(type.module_or_class)}.#{name}"
        elsif type.is_a? KatakataIrb::Types::InstanceType
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

      value_doc = -> type do
        return unless type
        type.types.each do |t|
          case t
          when KatakataIrb::Types::SingletonType
            return KatakataIrb::Types.class_name_of(t.module_or_class)
          when KatakataIrb::Types::InstanceType
            return KatakataIrb::Types.class_name_of(t.klass)
          when KatakataIrb::Types::ProcType
            return 'Proc'
          end
        end
        nil
      end

      case KatakataIrb::Completor.prev_analyze_result
      in [:call_or_const, type, _name, _self_call]
        call_or_const_doc.call type
      in [:const, type, _name, scope]
        if type
          call_or_const_doc.call type
        else
          value_doc.call scope[name]
        end
      in [:gvar, _name, scope]
        value_doc.call scope["$#{name}"]
      in [:ivar, _name, scope]
        value_doc.call scope["@#{name}"]
      in [:cvar, _name, scope]
        value_doc.call scope["@@#{name}"]
      in [:call, type, _name, _self_call]
        method_doc.call type
      in [:lvar_or_method, _name, scope]
        if scope.local_variables.include?(name)
          value_doc.call scope[name]
        else
          method_doc.call scope.self_type
        end
      else
      end
    end

    if IRB.const_defined? :RegexpCompletor # IRB::VERSION >= 1.8.2
      IRB::RegexpCompletor.class_eval do
        define_method :completion_candidates do |preposing, target, postposing, bind:|
          completion_proc.call(preposing, target, postposing, bind: bind)
        end
        define_method :doc_namespace do |_preposing, matched, _postposing, bind:|
          doc_namespace_proc.call matched
        end
      end
    elsif IRB.const_defined? :InputCompletor # IRB::VERSION <= 1.8.1
      IRB::InputCompletor::CompletionProc.define_singleton_method :call do |target, preposing = '', postposing = ''|
        bind = IRB.conf[:MAIN_CONTEXT].workspace.binding
        completion_proc.call(preposing, target, postposing, bind: bind)
      end
      IRB::InputCompletor.singleton_class.prepend(
        Module.new do
          define_method :retrieve_completion_data do |input, doc_namespace: false, **kwargs|
            return super(input, doc_namespace: false, **kwargs) unless doc_namespace
            doc_namespace_proc.call input
          end
        end
      )
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

  def self.analyze(code, binding = Object::TOPLEVEL_BINDING)
    # Workaround for https://github.com/ruby/prism/issues/1592
    return if code.match?(/%[qQ]\z/)

    lvars_code = binding.local_variables.map do |name|
      "#{name}="
    end.join + "nil;\n"
    code = lvars_code + code
    ast = Prism.parse(code).value
    name = code[/(@@|@|\$)?\w*[!?=]?\z/]
    *parents, target_node = find_target ast, code.bytesize - name.bytesize
    return unless target_node

    calculate_scope = -> { KatakataIrb::TypeAnalyzer.calculate_target_type_scope(binding, parents, target_node).last }
    calculate_type_scope = ->(node) { KatakataIrb::TypeAnalyzer.calculate_target_type_scope binding, [*parents, target_node], node }

    case target_node
    when Prism::StringNode, Prism::InterpolatedStringNode
      call_node, args_node = parents.last(2)
      return unless call_node.is_a?(Prism::CallNode) && call_node.receiver.nil?
      return unless args_node.is_a?(Prism::ArgumentsNode) && args_node.arguments.size == 1

      case call_node.name
      when :require
        [:require, name.rstrip]
      when :require_relative
        [:require_relative, name.rstrip]
      end
    when Prism::SymbolNode
      if parents.last.is_a? Prism::BlockArgumentNode # method(&:target)
        receiver_type, _scope = calculate_type_scope.call target_node
        [:call, receiver_type, name, false]
      else
        [:symbol, name] unless name.empty?
      end
    when Prism::CallNode
      return [:lvar_or_method, name, calculate_scope.call] if target_node.receiver.nil?

      self_call = target_node.receiver.is_a? Prism::SelfNode
      op = target_node.call_operator
      receiver_type, _scope = calculate_type_scope.call target_node.receiver
      receiver_type = receiver_type.nonnillable if op == '&.'
      [op == '::' ? :call_or_const : :call, receiver_type, name, self_call]
    when Prism::LocalVariableReadNode, Prism::LocalVariableTargetNode
      [:lvar_or_method, name, calculate_scope.call]
    when Prism::ConstantReadNode, Prism::ConstantTargetNode
      if parents.last.is_a? Prism::ConstantPathNode
        path_node = parents.last
        if path_node.parent # A::B
          receiver, scope = calculate_type_scope.call(path_node.parent)
          [:const, receiver, name, scope]
        else # ::A
          scope = calculate_scope.call
          [:const, KatakataIrb::Types::SingletonType.new(Object), name, scope]
        end
      else
        [:const, nil, name, calculate_scope.call]
      end
    when Prism::GlobalVariableReadNode, Prism::GlobalVariableTargetNode
      [:gvar, name, calculate_scope.call]
    when Prism::InstanceVariableReadNode, Prism::InstanceVariableTargetNode
      [:ivar, name, calculate_scope.call]
    when Prism::ClassVariableReadNode, Prism::ClassVariableTargetNode
      [:cvar, name, calculate_scope.call]
    end
  end

  def self.find_target(node, position)
    location = (
      case node
      when Prism::CallNode
        node.message_loc
      when Prism::SymbolNode
        node.value_loc
      when Prism::StringNode
        node.content_loc
      when Prism::InterpolatedStringNode
        node.closing_loc if node.parts.empty?
      end
    )
    return [node] if location&.start_offset == position

    node.child_nodes.each do |n|
      next unless n.is_a? Prism::Node
      match = find_target(n, position)
      next unless match
      match.unshift node
      return match
    end

    [node] if node.location.start_offset == position
  end
end
