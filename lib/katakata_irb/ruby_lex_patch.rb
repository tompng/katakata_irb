require 'irb'
require_relative 'trex'

module KatakataIrb::RubyLexPatch
  def self.patch_to_ruby_lex
    (RubyLex.instance_methods(false) - [:set_prompt, :process_continue, :check_code_block]).each { RubyLex.remove_method _1 }
    RubyLex.prepend self
  end

  def self.complete_tokens(code, context: nil)
    incomplete_tokens = RubyLex.ripper_lex_without_warning(code, context: context)
    KatakataIrb::TRex.interpolate_ripper_ignored_tokens(code, incomplete_tokens)
  end

  def calc_nesting_depth(opens)
    indent_level = 0
    nesting_level = 0
    opens.each_with_index do |t, index|
      case t.event
      when :on_heredoc_beg
        if opens[index + 1]&.event != :on_heredoc_beg
          if t.tok.start_with?('<<~')
            indent_level += 1
          else
            indent_level = 0
          end
        end
      when :on_tstring_beg, :on_regexp_beg, :on_symbeg
        indent_level += 1 if t.tok[0] == '%'
      when :on_embdoc_beg
        indent_level = 0
      else
        nesting_level += 1
        indent_level += 1
      end
    end
    [indent_level, nesting_level]
  end

  def process_indent_level(tokens)
    opens = KatakataIrb::TRex.parse(tokens)
    indent, _nesting = calc_nesting_depth(opens)
    indent * 2
  end

  def check_corresponding_token_depth(tokens, line_index)
    line_results = KatakataIrb::TRex.parse_line(tokens)
    result = line_results[line_index]
    return unless result
    _tokens, prev, opens, min_depth = result
    depth, = calc_nesting_depth(opens.take(min_depth))
    prev_depth, = calc_nesting_depth(prev)
    depth * 2 if depth < prev_depth
  end

  def ltype_from_open_tokens(opens)
    return nil if opens.empty?
    case opens.last.tok
    when ?`, /^<<[-~]?`/, /^%x.$/
      ?`
    when ?', /^<<[-~]?'/, /^%q.$/
      ?'
    when ?", /^<</, /^%.$/, /^%Q.$/
      ?"
    when ":'", ':"', ':', /^%s.$/
      ':'
    when /^%[iwIW].$/
      ']'
    when '/', /^%r.$/
      '/'
    end
  end

  def check_termination_in_prev_line(code, context: nil)
    tokens = self.class.ripper_lex_without_warning(code, context: context)
    last_newline_index = tokens.rindex { |t| t.tok.include?("\n") }
    index = (0...last_newline_index).reverse_each.find { |i| tokens[i].tok.include?("\n") }
    return false unless index

    last_line_tokens = tokens[(index + 1)..(tokens.size - 1)]
    first_token = last_line_tokens.find do |t|
      ![:on_sp, :on_ignored_sp, :on_comment].include?(t.event)
    end

    if first_token && first_token.state != Ripper::EXPR_DOT
      tokens_without_last_line = tokens[0..index]
      if check_termination(tokens_without_last_line)
        return last_line_tokens.map(&:tok).join
      end
    end
    false
  end

  def check_termination(tokens)
    opens = KatakataIrb::TRex.parse(tokens)
    opens.empty? && !process_continue(tokens)
  end

  def set_input(io, p = nil, context: nil, &block)
    @io = io
    if @io.respond_to?(:check_termination)
      @io.check_termination do |code|
        if Reline::IOGate.in_pasting?
          lex = RubyLex.new
          rest = lex.check_termination_in_prev_line(code, context: context)
          if rest
            Reline.delete_text
            rest.bytes.reverse_each do |c|
              Reline.ungetc(c)
            end
            true
          else
            false
          end
        else
          tokens = KatakataIrb::RubyLexPatch.complete_tokens(code, context: context)
          check_termination(tokens)
        end
      end
    end
    if @io.respond_to?(:dynamic_prompt)
      @io.dynamic_prompt do |lines|
        lines << '' if lines.empty?
        code = lines.map{ |l| l + "\n" }.join
        tokens = KatakataIrb::RubyLexPatch.complete_tokens code, context: context
        line_results = KatakataIrb::TRex.parse_line(tokens)
        continue = false
        tokens_until_line = []
        line_results.map.with_index do |(line_tokens, _prev_opens, next_opens), line_num_offset|
          line_tokens.each do |token, _s|
            tokens_until_line << token if token != tokens_until_line.last
          end
          unless (c = process_continue(tokens_until_line)).nil?
            continue = c
          end
          prompt next_opens, continue, line_num_offset
        end
      end
    end

    if p.respond_to?(:call)
      @input = p
    elsif block_given?
      @input = block
    else
      @input = Proc.new{@io.gets}
    end
  end

  def set_auto_indent(context)
    if @io.respond_to?(:auto_indent) and context.auto_indent_mode
      @io.auto_indent do |lines, line_index, byte_pointer, is_newline|
        if is_newline
          tokens = KatakataIrb::RubyLexPatch.complete_tokens(lines[0..line_index].join("\n"), context: context)
          process_indent_level tokens
        else
          code = line_index.zero? ? '' : lines[0..(line_index - 1)].map{ |l| l + "\n" }.join
          last_line = lines[line_index]&.byteslice(0, byte_pointer)
          code += last_line if last_line
          tokens = KatakataIrb::RubyLexPatch.complete_tokens(code, context: context)
          check_corresponding_token_depth(tokens, line_index)
        end
      end
    end
  end

  def prompt(opens, continue, line_num_offset)
    ltype = ltype_from_open_tokens(opens)
    _indent, nesting_level = calc_nesting_depth(opens)
    @prompt.call(ltype, nesting_level, opens.any? || continue, @line_no + line_num_offset)
  end

  def store_prompt_to_irb(...)
    prompt(...) # TODO: do not use this. change the api. example: @input.call(prompt)
  end

  def readmultiline(context)
    if @io.respond_to? :check_termination
      store_prompt_to_irb [], false, 0
      @input.call
    else
      # nomultiline
      line = ''
      line_offset = 0
      store_prompt_to_irb [], false, 0
      loop do
        l = @input.call
        unless l
          return if line.empty?
          next
        end
        line << l
        tokens = KatakataIrb::RubyLexPatch.complete_tokens(line, context: context)
        _line_tokens, _prev_opens, next_opens = KatakataIrb::TRex.parse_line(tokens).last
        return line if next_opens.empty?
        line_offset += 1
        store_prompt_to_irb next_opens, true, line_offset
      end
    end
  end

  def each_top_level_statement(context = nil)
    loop do
      begin
        line = readmultiline(context)
        break unless line
        if line != "\n"
          line.force_encoding(@io.encoding)
          yield line, @line_no
        end
        @line_no += line.count("\n")
      rescue RubyLex::TerminateLineInput
      end
    end
  end
end
