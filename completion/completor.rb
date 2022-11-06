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
    last_opens, unclosed_heredocs = TRex.parse(tokens)
    closing_heredocs = unclosed_heredocs.map {|t|
      t.tok.match(/\A<<(?:"(?<s>.+)"|'(?<s>.+)'|(?<s>.+))/)[:s]
    }
    closings = last_opens.map do |t,|
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
      [:call, Completion::TypeSimulator.simulate_evaluate(receiver, binding, lvar_available, icvar_available), name]
    in [:const_path_ref, receiver, [:@const,]]
      [:const, Completion::TypeSimulator.simulate_evaluate(receiver, binding, lvar_available, icvar_available), name]
    in [:def,] | [:string_content,] | [:var_field,] | [:defs,] | [:rest_param,] | [:kwrest_param,] | [:blockarg,] | [[:@ident,],]
    else
      STDERR.cooked{
        STDERR.puts
        STDERR.puts [:NEW_EXPRESSION, expression].inspect
        STDERR.puts
      }
    end
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

  exit
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
  p Completion::Completor.analyze tokens
end
