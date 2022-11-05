require_relative './trex'

module RubyLexPatch
  def calc_nesting_depth(tokens)
    indent_level = 0
    nesting_level = 0
    tokens.each_with_index do |t, index|
      case t.event
      when :on_heredoc_beg
        if tokens[index + 1]&.event != :on_heredoc_beg
          if t.tok.start_with?('<<~')
            indent_level += 1
          else
            indent_level = 0
          end
        end
      when :on_tstring_beg, :on_regexp_beg
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
    opens, heredocs = TRex.parse(tokens){}
    indent, _nesting = calc_nesting_depth(opens.map(&:first) + heredocs)
    indent * 2
  end

  def check_corresponding_token_depth(tokens, line_index)
    lines, = TRex.parse_line(tokens)
    result = lines[line_index]
    return unless result
    _tokens, prev, opens, min_depth = result
    depth, = calc_nesting_depth(opens.take(min_depth).map(&:first))
    prev_depth, = calc_nesting_depth(prev.map(&:first))
    depth * 2 if depth < prev_depth
  end

  def check_string_literal(tokens)
    TRex.parse(tokens){}.first.map(&:first).reverse.find do |t, _state|
      %i[on_tstring_beg on_regexp_beg on_symbeg on_backtick on_qwords_beg on_words_beg on_qsymbols_beg on_symbols_beg on_heredoc_beg].include? t.event
    end
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
    when ":'", ':"', ':', /^%s$/
      ':'
    when /^%[iwIW]$/
      ']'
    when '/', /^%r.$/
      '/'
    end
  end

  def check_termination_in_prev_line(code, context: nil)
    tokens = self.class.ripper_lex_without_warning(code, context: context)
    lines, = TRex.parse_line(tokens)
    if lines[-2]&.[](2)&.empty?
      lines[-1].first.map(&:last).join
    else
      false
    end
  end

  def check_termination(code, context: nil)
    tokens = self.class.ripper_lex_without_warning(code, context: context)
    opens, heredocs = TRex.parse(tokens){}
    opens.empty? && heredocs.empty?
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
          check_termination(code, context: context)
        end
      end
    end
    if @io.respond_to?(:dynamic_prompt)
      @io.dynamic_prompt do |lines|
        lines << '' if lines.empty?
        code = lines.map{ |l| l + "\n" }.join
        tokens = self.class.ripper_lex_without_warning code
        lines, _unclosed_heredocs = TRex.parse_line(tokens)
        lines.map.with_index do |(_line, _prev_opens, next_opens), line_num_offset|
          prompt next_opens, line_num_offset
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
          tokens = self.class.ripper_lex_without_warning(lines[0..line_index].join("\n"), context: context)
          process_indent_level tokens
        else
          code = line_index.zero? ? '' : lines[0..(line_index - 1)].map{ |l| l + "\n" }.join
          last_line = lines[line_index]&.byteslice(0, byte_pointer)
          code += last_line if last_line
          tokens = self.class.ripper_lex_without_warning(code, context: context)
          check_corresponding_token_depth(tokens, line_index)
        end
      end
    end
  end

  def prompt(opens, line_num_offset)
    ltype = ltype_from_open_tokens opens.map(&:first)
    _indent, nesting_level = calc_nesting_depth opens.map(&:first)
    @prompt.call(ltype, nesting_level, opens.any?, @line_no + line_num_offset)
  end

  def readmultiline(context)
    if @io.respond_to? :check_termination # multiline
      loop do
        @prompt.call(nil, 0, true, @line_no)
        input = @input.call
        return input if input
      end
    end
    line = ''
    line_offset = 0
    @prompt.call(nil, 0, true, @line_no)
    loop do
      l = @input.call
      next if l.nil?
      line << l
      tokens = self.class.ripper_lex_without_warning(line, context: context)
      _prev_opens, next_opens = TRex.parse_line(tokens).first.last
      return line if next_opens.empty?
      prompt next_opens, line_offset
      line_offset += 1
    end
  end

  def each_top_level_statement(context)
    initialize_input
    loop do
      begin
        line = readmultiline(context)
        if line != "\n"
          line.force_encoding(@io.encoding)
          yield line, @line_no
        end
        @line_no += line.count("\n")
        raise RubyLex::TerminateLineInput if @io.eof?
      rescue RubyLex::TerminateLineInput
        initialize_input
      end
    end
  end
end
