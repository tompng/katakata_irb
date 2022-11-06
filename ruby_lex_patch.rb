require_relative 'trex'

module RubyLexPatch
  def self.patch_to_ruby_lex
    (RubyLex.instance_methods(false) - [:initialize_input, :set_prompt]).each { RubyLex.remove_method _1 }
    RubyLex.prepend self
  end

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
    opens, heredocs = TRex.parse(tokens)
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
    *lines, last_line = code.lines
    last_line if lines.any? && check_termination(lines.join, context: context)
  end

  def check_termination(code, context: nil)
    tokens = self.class.ripper_lex_without_warning(code, context: context)
    opens, heredocs = TRex.parse(tokens)
    opens.empty? && heredocs.empty? && !check_continue(tokens)
  end

  def check_continue(tokens)
    last_token = tokens.reverse_each.find { !(_1.event in :on_sp | :on_nl | :on_ignored_nl) }
    return unless last_token # should return nil
    last_token.state.allbits?(Ripper::EXPR_BEG) || last_token.state.allbits?(Ripper::EXPR_DOT)
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
        continue = false
        lines.map.with_index do |(line, _prev_opens, next_opens), line_num_offset|
          unless (c = check_continue(line.map(&:first))).nil?
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

  def prompt(opens, continue, line_num_offset)
    ltype = ltype_from_open_tokens opens.map(&:first)
    _indent, nesting_level = calc_nesting_depth opens.map(&:first)
    @prompt.call(ltype, nesting_level, opens.any? || continue, @line_no + line_num_offset)
  end

  def store_prompt_to_irb(...)
    prompt(...) # TODO: do not use store, change API. example: @input.call(prompt)
  end

  def readmultiline(context)
    if @io.respond_to? :check_termination
      loop do
        store_prompt_to_irb [], false, 0
        input = @input.call
        return input if input
      end
    else
      # nomultiline
      line = ''
      line_offset = 0
      store_prompt_to_irb [], false, 0
      loop do
        l = @input.call
        next if l.nil?
        line << l
        tokens = self.class.ripper_lex_without_warning(line, context: context)
        _line, _prev_opens, next_opens = TRex.parse_line(tokens).first.last
        return line if next_opens.empty?
        line_offset += 1
        store_prompt_to_irb next_opens, true, line_offset
      end
    end
  end

  def each_top_level_statement(context = nil)
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
