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
    return [OBJECT_METHODS[method]] if OBJECT_METHODS.has_key? method
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
  end

  def self.stree(tokens)
    stack = [[]]
    last_opens, _unclosed_heredocs = TRex.parse tokens do |t, _index, opens|
      if stack.size > opens.size + 1
        stack.last << t
        stack.pop
      elsif stack.size < opens.size + 1
        a = [t]
        stack.last << a
        stack << a
      else
        stack.last << t
      end
    end
    [stack, last_opens]
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

  def self.analyze(tokens, binding = Kernel.binding)
    tokens = tokens.reject { _1 in { event: :on_ignored_nl | :on_comment | [{ event: :on_heredoc_beg | :on_embdoc_beg }, *] }}
    stack, opens = stree tokens
    tree = stack.last
    return if tree.empty?
    case opens.last&.first&.event
    when :on_tstring_beg
      if (
          tree in [{ event: :on_tstring_beg }, { event: :on_tstring_content, tok: target }]
        ) && (
          stack[-2].reject {|t| t in { event: :on_sp }} in [*, { event: :on_ident, tok: 'require' | 'require_relative' => method }, Array]
        )
        return [:require, method, target]
      end
    when :on_symbeg
      # unclosed `:"symbol"`, `%s[symbol]`
      if tree in [{ event: :on_symbeg }, { event: :on_tstring_content } => t]
        return [:symbol, t.tok]
      else
        return
      end
    end
    case tree
    in [*prev, { event: :on_sp }, { event: :on_op, tok: '::' } => dot, { event: :on_const, tok: name }]
      [:cosnt, name] # TODO (::Const) (exp;::Const)
    in [*prev, { event: :on_op, tok: '::' } => dot, { event: :on_const | :on_ident | :on_kw | :on_op, tok: name }]
      [:cosnt, name]
    in [*prev, { event: :on_period } | { event: :on_op, tok: '::' } => dot, { event: :on_ident, tok: name }]
      [:method_call_or_const_accessor, dot.tok, name, receiver(prev, binding)]
    in [*prev, { event: :on_period } | { event: :on_op, tok: '::' } => dot]
      [:method_call_or_const_accessor, dot.tok, '', receiver(prev, binding)]
    in [*prev, [{ event: :on_symbeg }, { event: :on_kw | :on_ident | :on_const | :on_gvar, tok: name }]]
      [:symbol, name]
    in [*prev, { event: :on_int }]
      [:int_or_int_method_call]
    else
      return
    end
  end

  def self.receiver(tree, binding)
    receiver, method_chains = get_receiver_method_chains tree
    type = receiver_type receiver, binding
    types = type ? [type] : []
    method_chains.each do |_dot, method, _args, _block, bracket|
      if method
        # Kernel.binding.irb
        types = types.flat_map do |klass|
          method_response klass, method.tok.to_sym
        end.uniq
      end
      if bracket
        types = types.flat_map do |klass|
          method_response klass, :[]
        end.uniq
      end
    end
    types
  end

  def self.receiver_type(receiver, binding)
    case receiver
    in [{ event: :on_tlambeg | :on_tstring_beg | :on_symbeg | :on_backtick | :on_regexp_beg | :on_words_beg | :on_qwords_beg | :on_symbols_beg | :on_qsymbols_beg } => t, *]
      { on_tlambeg: Proc, on_tstring_beg: String, on_symbeg: Symbol, on_backtick: String, on_regexp_beg: Regexp, on_words_beg: Array, on_qwords_beg: Array, on_symbols_beg: Array, on_qsymbols_beg: Array }[t.event]
    in { event: :on_CHAR | :on_int | :on_float | :on_rational | :on_imaginary | :on_heredoc_beg }
      { on_CHAR: String, on_int: Integer, on_float: Float, on_rational: Rational, on_imaginary: Complex, on_herdoc_beg: String }[receiver.event]
    in { event: :on_kw, tok: 'nil' | 'true' | 'false' }
      { 'nil' => NilClass, 'true' => TrueClass, 'false' => FalseClass }[receiver.tok]
    in { event: :on_cvar | :on_ivar | :on_gvar | :on_ident, tok: }
      binding.eval(tok).class rescue nil
    in { event: :on_ident, tok: }
      binding.eval(tok).class if binding.local_variables.include? tok
    in [{ event: :on_kw }, *] |
      nil
    in [{ event: :on_lbracket, label: true }, *] |
      Hash
    in [{ event: :on_lparen }, *]
      nil # not implemented
    else
      nil
    end
  end

  def self.parse(tree)
    # if tree.
    # p tree
    # case tree
    # in [{ event: :lparen}, *inner, {}]
    #   parse inner
    # in [receiver, { event: :period }, { tok: method }, *rest]
    #   { receive: parse(receiver), method:, parse
  end

  def self.hoge(tree, binding)
    return [] unless tree
    tree = tree.dup
    first_token = tree.shift
    receiver = case first_token
    in { event: :on_int }
      Integer
    in { event: :on_float }
      Float
    in { event: :on_rational }
      Rational
    in { event: :on_imaginary }
      Complex
    in { event: :on_CHAR | :on_heredoc_beg } | [{ event: :on_tstring_beg | :on_backtick }, *]
      String
    in { event: :on_ident, tok: 'proc' | 'lambda' }
      Proc # or localvar?
    in { event: :on_ident, tok: }
      binding.local_variables.include?(tok.to_sym) ? binding.eval(tok).class : nil
    in { event: :on_const, tok: }
      begin
        const = Object.const_get(tok)
        const.is_a?(Module) ? { class: const } : const.class
      rescue
      end
    in { event: :on_ivar | :on_gvar, tok: }
      binding.eval(tok).class rescue nil
    in [{ event: :on_tlambeg }, *]
      Proc
    in [{ event: :on_regexp_beg }, *]
      Regexp
    in [{ event: :on_symbeg }, *]
      Symbol
    in [{ event: :on_lbracket | :on_words_beg | :on_qwords_beg | :on_symbols_beg | :on_qsymbols_beg }, *]
      Array
    in [{ event: :on_lbrace }, *]
      Hash
    else
    end
    return [] unless receiver
    receiver_types = [receiver]
    tree.each do |t|
      if t in [{ event: :on_lbracket }, *]
        method = :[]
      elsif t in { event: :on_ident | :on_op | :on_kw, tok: }
        method = tok.to_sym
      end
      if method
        receiver_types = receiver_types.flat_map do |klass|
          method_response klass, method
        end.uniq
      end
    end
    receiver_types
  end

  DOT = -> { _1 in { event: :on_period, dot: true } | { event: :on_op, top: '::', dot: true } }
  METHOD = -> { _1 in { event: :on_kw | :on_ident | :on_const | :on_op } }
  BLOCK = -> { _1 in [{ event: :on_lbrace, label: false }, *] | [{ event: :on_kw, tok: 'do' }, *] }
  PAREN = -> { _1 in [{ event: :on_lparen }, *] }
  BRACKET = -> { _1 in [{ event: :on_lbracket }, *] }

  def self.tail_match(tree, matchers)
    idx = tree.size - 1
    matched = matchers.reverse_each.map do |m|
      idx -= 1 while idx >= 0 && tree[idx] in { event: :on_sp }
      return nil unless idx >= 0 && (m.nil? || m.call(tree[idx]))
      if m
        idx -= 1
        tree[idx + 1]
      end
    end
    [matched.reverse, tree.size - idx - 1]
  end

  def self.get_receiver_method_chains(tree)
    end_idx = tree.rindex { _1 in { event: :on_semicolon | :on_nl } | { event: :on_kw, tok: 'if' | 'while' | 'unless' | 'until' | 'rescue', label: true } }
    tree = end_idx ? tree[end_idx + 1..] : tree.dup

    receiver_pattern = -> do
      _1 in [{ event: :on_tlambeg | :on_tstring_beg | :on_symbeg | :on_backtick | :on_regexp_beg | :on_words_beg | :on_qwords_beg | :on_symbols_beg | :on_qsymbols_beg }, *] |
            { event: :on_CHAR | :on_int | :on_float | :on_rational | :on_imaginary | :on_heredoc_beg } |
            { event: :on_kw, tok: 'nil' | 'true' | 'false' } |
            { event: :on_cvar | :on_ivar | :on_gvar } |
            [{ event: :on_kw }, *] |
            [{ event: :on_lbracket, label: true }, *] |
            [{ event: :on_lparen }, *]
    end

    method_chain = []
    while true
      matched, size =
        tail_match(tree, [DOT, METHOD, PAREN, BLOCK, BRACKET]) ||
        tail_match(tree, [DOT, METHOD, PAREN, nil, BRACKET]) ||
        tail_match(tree, [DOT, METHOD, nil, nil, BRACKET]) ||
        tail_match(tree, [DOT, METHOD, PAREN, BLOCK, nil]) ||
        tail_match(tree, [DOT, METHOD, nil, BLOCK, nil]) ||
        tail_match(tree, [DOT, METHOD, PAREN, nil, nil]) ||
        tail_match(tree, [DOT, METHOD, nil, nil, nil])
      if matched
        method_chain.unshift matched
        tree = tree[0...-size]
      elsif (matched, = tail_match tree, [receiver_pattern])
        return [matched[0], method_chain]
      else
        return [nil, method_chain] # unknown receiver
      end
    end
  end

  def self.patch_to_completor
    completion_proc = ->(target, preposing = nil, postposing = nil) do
      code = "#{preposing}#{target}"
      tokens = RubyLex.ripper_lex_without_warning code
      result = analyze tokens, IRB.conf[:MAIN_CONTEXT].workspace.binding
      case result
      in [:int_or_int_method_call]
        if target.end_with? '.'
          Integer.instance_methods.sort.map do
            target + _1.to_s
          end
        else
          []
        end
      in [:require, method, lib]
        ['irb', 'reline']
      in [:symbol, name]
        ['hoge', 'fuga']
      in [:method_call_or_const_accessor, dot, name, classes]
        candidates = classes.flat_map do |k|
          if k in { class: klass }
            klass.methods
          else
            k.instance_methods
          end
        end
        candidates.select { _1.start_with? name }.uniq.sort.map do
          target + _1[name.size..]
        end
      else
        []
      end
    end
    IRB::InputCompletor.const_set :CompletionProc, completion_proc
  end

  def self.analyze2(tokens)
    last_opens, unclosed_heredocs = TRex.parse(tokens){ }
    closing_heredocs = unclosed_heredocs.map {|t|
      "\n#{t.tok.match(/\A<<(?:"(?<s>.+)"|'(?<s>.+)'|(?<s>.+))/)[:s]}\n"
    }
    closings = last_opens.map do |t,|
      case t.tok
      when /[{}]/
        '}'
      when /[()]/
        ')'
      when /[\[\]]/
        ']'
      when /\A%.*(.)/
        $1
      else
        ';end;'
      end
    end
    code = tokens.map(&:tok).join + 'xxxxxx' + closing_heredocs.reverse.join + closings.reverse.join
    puts code
    sexp = Ripper.sexp code
    binding.irb
  end

end

if $0 == __FILE__
  code = <<~'RUBY'.chomp
    if true
      10.times do |i|
        ([1, 2, ((3+(i.times.map{}.size+4)*5.to_i).itself
        hoge
        %[]
        %w[]; %W[]; %Q[]; %s[]; %i[]; %I[]+A::DATA
        .times do
        end[0].a(1).b{2}.c[3].d{4}[5].e
        123.to_f.hoge
        %[].aa
        '$hello'.to_s.size.times.map.to_a.hoge
  RUBY
  tokens = RubyLex.ripper_lex_without_warning(code)
  # p Completion.stree tokens
  p Completion.analyze tokens
end
