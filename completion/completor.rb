require_relative '../trex'
require_relative 'type_simulator'
require 'rbs'
require 'rbs/cli'
require 'irb'
module Completion; end
module Completion::Completor
  using Completion::TypeSimulator::LexerElemMatcher

  def self.patch_to_completor
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
        (self_call ? type.all_methods : type.methods) | type.constants
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
        Symbol.all_symbols.reject { _1.match? '_trex_completion_' }
      in [:call, type, name, self_call]
        self_call ? type.all_methods : type.methods
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
    end
  end

  def self.analyze(code, binding = Kernel.binding)
    lvars_code = binding.local_variables.map do |name|
      "#{name}="
    end.join + "nil;\n"
    code = lvars_code + code
    tokens = RubyLex.ripper_lex_without_warning code
    tokens = TRex.interpolate_ripper_ignored_tokens code, tokens
    last_opens, unclosed_heredocs = TRex.parse(tokens)
    closings = (last_opens + unclosed_heredocs).map do |t,|
      case t.tok
      when /\A%.[<>]\z/
        '>'
      when '{', '#{', /\A%.[{}]\z/
        '}'
      when '(', /\A%.[()]\z/
        ')'
      when '[', /\A%.[\[\]]\z/
        ']'
      when /\A%.?(.)\z/
        $1
      when '"', "'"
        t.tok
      when /\A<<(?:"(?<s>.+)"|'(?<s>.+)'|(?<s>.+))/
        $3
      else
        'end'
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

    closings = $/ + closings.reverse.join($/)
    sexp = Ripper.sexp code + suffix + closings
    lines = code.lines
    line_no = lines.size
    col = lines.last.bytesize
    if lines.last.end_with? "\n"
      line_no += 1
      col = 0
    end

    if sexp in [:program, [lvars_exp, *rest_statements]]
      sexp = [:program, rest_statements]
    end

    *parents, expression, target = find_target sexp, line_no, col
    in_class_module = parents&.any? { _1 in [:class | :module,] }
    icvar_available = !in_class_module
    return unless target in [type, String, [Integer, Integer]]
    if target in [:@ivar,]
      return [:ivar, name] if icvar_available
    elsif target in [:@cvar,]
      return [:cvar, name] if icvar_available
    end
    return unless expression
    if (target in [:@tstring_content,]) && (parents[-4] in [:command, [:@ident, 'require' | 'require_relative' => require_method,],])
      return [require_method.to_sym, name.rstrip]
    end
    calculate_scope = -> { Completion::TypeSimulator.calculate_binding_scope binding, parents, expression }
    calculate_receiver = -> receiver { Completion::TypeSimulator.calculate_receiver binding, parents, receiver }
    case expression
    in [:vcall | :var_ref, [:@ident,]]
      [:lvar_or_method, name, calculate_scope.call]
    in [:symbol, [:@ident | :@const | :@op | :@kw,]]
      [:symbol, name]
    in [:var_ref | :const_ref, [:@const,]]
      # TODO
      [:const, Completion::Types::SingletonType.new(Object), name]
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
    in [:def,] | [:string_content,] | [:var_field,] | [:defs,] | [:rest_param,] | [:kwrest_param,] | [:blockarg,] | [[:@ident,],]
    else
      STDERR.cooked{
        STDERR.puts
        STDERR.puts [:NEW_EXPRESSION, expression].inspect
        STDERR.puts
      }
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

if $0 == __FILE__
=begin
  classes = ObjectSpace.each_object(Class)
  Completion::Completor.class_eval do
    return_types = []
    method_types = []
    classes.each do |klass|
      next unless klass.name
      type_name = RBS::TypeName(klass.name).absolute!
      mdefinition = Completion::Types.rbs_builder.build_singleton type_name rescue nil
      idefinition = Completion::Types.rbs_builder.build_instance type_name rescue nil
      [mdefinition, idefinition].compact.each do |definition|
        definition.methods.each_value do |method|
          method.method_types.each do
            method_types << _1.type
            return_types << _1.type.return_type
          end
        end
      end
    end
    return_types.uniq!
    binding.irb
  end
=end
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
  p Completion::Completor.analyze code
end
