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
      # t = t.tok
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
      def deconstruct_keys(...) = { tok: tok, event: event }.deconstruct_keys(...)
    end
  end

  using LexerElemMatcher

  def self.analyze(tokens)
    stack, opens = stree tokens
    tree = stack.last
    return if tree.empty?
    case opens.last&.first&.event
    when :on_tstring_beg
      if (
          tree in [{ event: :on_tstring_beg }, { event: :on_tstring_content, tok: target }]
        ) && (
          (stack[-2] in [*, { event: :on_ident, tok: 'require' | 'require_relative' => method }, { event: :on_sp }, Array]) ||
          (stack[-2] in [*, { event: :on_ident, tok: 'require' | 'require_relative' => method }, Array])
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
    in [*prev, { event: :on_period } | { event: :on_op, tok: '::' } => dot, { event: :on_ident, tok: name }]
      [:method_call_or_const_accessor, dot, name, receiver(prev)]
    in [*prev, { event: :on_period } | { event: :on_op, tok: '::' } => dot, { event: :on_sp | :on_ignored_nl }, { event: :on_ident, tok: name }]
      [:method_call_or_const_accessor, dot, name, receiver(prev)]
    in [*prev, { event: :on_period } | { event: :on_op, tok: '::' } => dot]
      [:method_call_or_const_accessor, dot, receiver(prev)]
    in [*prev, [{ event: :on_symbeg }, { event: :on_kw | :on_ident | :on_const | :on_gvar, tok: name }]]
      [:symbol, name]
    in [*prev, { event: :on_int }]
      [:int_or_int_method_call]
    else
      return
    end
  end

  def self.receiver(tree, binding = Kernel.binding)
    receiver_type receiver_tree(tree), binding
  end

  def self.receiver_type(tree, binding)
    return unless tree
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
        const = binding.const_get(tok)
        const.is_a?(Module) ? { class: const } : const.class
      rescue
        nil
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
      nil
    end
    receiver_types = [receiver]
    tree.each do |t|
      if t in [{ event: :on_lbracket }, *]
        method = :[]
      elsif t in { event: :on_ident | :on_op | :on_kw, tok: }
        method = tok.to_sym
      end
      if method
        receiver_types2 = receiver_types.flat_map do |klass|
          method_response klass, method
        end.uniq
        # Kernel.binding.irb
        receiver_types = receiver_types2
      end
    end
    receiver_types
  end

  def self.receiver_tree(tree)
    tree = tree.dup.reject { _1 in { event: :on_sp | :on_ignored_nl | :on_comment | [{ event: :on_heredoc_beg }, *] }}
    receiver = []
    while true
      last = tree.last
      break if tree.nil?
      if tree in [*prev, { event: :on_period } | { event: :on_op, tok: '::' } => dot, { event: :on_op | :on_ident | :on_const } => method]
        receiver.unshift dot, method
        tree = prev
      elsif last in (
        [{ event: :on_lparen }, *] |
        [{ event: :on_lbracket }, *] |
        [{ event: :on_lbrace }, *] |
        [{ event: :on_kw, tok: 'do' }, *]
      )
        receiver.unshift tree.pop
      elsif last in (
        [{ event: :on_tlambeg | :on_tstring_beg | :on_symbeg | :on_backtick | :on_regexp_beg | :on_words_beg | :on_qwords_beg | :on_symbols_beg | :on_qsymbols_beg }, *] |
        [{ event: :on_kw, tok: 'class' | 'module' | 'def' | 'for' | 'if' | 'elsif' | 'unless' | 'while' | 'until' | 'case' | 'in' | 'rescue' | 'ensure' }, *] |
        { event: :on_CHAR | :on_int | :on_float | :on_rational | :on_imaginary | :on_const | :on_ivar | :on_gvar | :on_heredoc_beg }
      )
        receiver.unshift last
        return receiver
      else
        break
      end
    end
    receiver
  end
end

if $0 == __FILE__
  code = <<~'RUBY'.chomp
    if true
      10.times do |i|
        ([1, 2, (3+(i.times.map{}.size+4)*5.to_i).itself
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
