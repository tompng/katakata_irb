require 'irb'
require_relative 'nesting_parser'

module KatakataIrb::RubyLexPatch
  def self.patch_to_ruby_lex
    (RubyLex.instance_methods(false) - [:set_prompt, :process_continue, :check_code_block]).each { RubyLex.remove_method _1 }
    RubyLex.prepend self
  end

  def self.complete_tokens(code, context: nil)
    incomplete_tokens = RubyLex.ripper_lex_without_warning(code, context: context)
    KatakataIrb::NestingParser.interpolate_ripper_ignored_tokens(code, incomplete_tokens)
  end

  def calc_nesting_depth(opens)
    indent_level = 0
    nesting_level = 0
    opens.each_with_index do |t, index|
      case t.event
      when :on_heredoc_beg
        if opens[index + 1]&.event != :on_heredoc_beg
          if t.tok.match?(/^<<[~-]/)
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

  def process_indent_level(tokens, lines, line_index, is_newline)
    line_results = KatakataIrb::NestingParser.parse_line(tokens)
    result = line_results[line_index]
    return unless result
    _tokens, prev_opens, next_opens, min_depth = result
    depth, = calc_nesting_depth(prev_opens.take(min_depth))
    prev_depth, = calc_nesting_depth(prev_opens)
    indent = 2 * [depth, prev_depth].min
    is_newline = false unless lines[line_index].empty?
    if prev_opens.last&.event == :on_heredoc_beg
      if prev_opens.size < next_opens.size || prev_opens.last == next_opens.last
        if is_newline && lines[line_index].empty? && line_results[line_index - 1][1].last != prev_opens.last
          # first line in heredoc
          indent
        else
          # accept extra indent spaces inside heredoc
          [indent, lines[line_index - (is_newline ? 1 : 0)][/^ */].length].max
        end
      else
        # heredoc close
        prev_opens.last.tok.match?(/^<<[~-]/) ? 2 * (prev_depth - 1) : 0
      end
    else
      indent
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
    when ":'", ':"', ':', /^%s.$/
      ':'
    when /^%[iwIW].$/
      ']'
    when '/', /^%r.$/
      '/'
    end
  end

  def terminated?(code)
    tokens = KatakataIrb::RubyLexPatch.complete_tokens(code, context: @context)
    opens = KatakataIrb::NestingParser.parse(tokens)
    opens.empty? && !process_continue(tokens) && !check_code_block(code, tokens)
  end

  def check_termination_in_prev_line(code)
    tokens = KatakataIrb::RubyLexPatch.complete_tokens(code, context: @context)
    last_newline_index = tokens.rindex { |t| t.tok.include?("\n") }
    index = (0...last_newline_index).reverse_each.find { |i| tokens[i].tok.include?("\n") }
    return false unless index

    last_line_tokens = tokens[(index + 1)..(tokens.size - 1)]
    first_token = last_line_tokens.find do |t|
      ![:on_sp, :on_ignored_sp, :on_comment].include?(t.event)
    end

    if first_token && first_token.state != Ripper::EXPR_DOT
      tokens_without_last_line = tokens[0..index]
      code_without_last_line = tokens_without_last_line.map(&:tok).join
      opens_without_last_line = KatakataIrb::NestingParser.parse(tokens_without_last_line)
      if opens_without_last_line.empty? && !process_continue(tokens_without_last_line) && !check_code_block(code_without_last_line, tokens_without_last_line)
        return last_line_tokens.map(&:tok).join
      end
    end
    false
  end

  def command?(code)
    # Accept any single-line input for symbol aliases or commands that transform args
    command = code.split(/\s/, 2).first
    @context.symbol_alias?(command) || @context.transform_args?(command)
  end

  def set_input(io, context: nil, &block)
    @context ||= context
    @io = io
    if @io.respond_to?(:check_termination)
      @io.check_termination do |code|
        if Reline::IOGate.in_pasting?
          rest = check_termination_in_prev_line(code)
          if rest
            Reline.delete_text
            rest.bytes.reverse_each do |c|
              Reline.ungetc(c)
            end
            true
          else
            false
          end
        elsif command?(code)
          true
        else
          code.gsub!(/\s*\z/, '').concat("\n")
          terminated?(code)
        end
      end
    end
    if @io.respond_to?(:dynamic_prompt)
      @io.dynamic_prompt do |lines|
        lines << '' if lines.empty?
        tokens = KatakataIrb::RubyLexPatch.complete_tokens(lines.map{ |l| l + "\n" }.join, context: @context)
        line_results = KatakataIrb::NestingParser.parse_line(tokens)
        tokens_until_line = []
        line_results.map.with_index do |(line_tokens, _prev_opens, next_opens), line_num_offset|
          line_tokens.each do |token, _s|
            tokens_until_line << token if token != tokens_until_line.last
          end
          continue = process_continue(tokens_until_line)
          prompt(next_opens, continue, line_num_offset)
        end
      end
    end

    if block_given?
      @input = block
    else
      @input = Proc.new{@io.gets}
    end
  end

  def set_auto_indent(_context = nil)
    if @io.respond_to?(:auto_indent) and @context.auto_indent_mode
      @io.auto_indent do |lines, line_index, byte_pointer, is_newline|
        next nil if !is_newline && lines[line_index]&.byteslice(0, byte_pointer)&.match?(/\A\s*\z/)
        code = lines[0..line_index].map { |l| "#{l}\n" }.join
        next nil if code == "\n"
        tokens = KatakataIrb::RubyLexPatch.complete_tokens(code, context: @context)
        process_indent_level(tokens, lines, line_index, is_newline)
      end
    end
  end

  def prompt(opens, continue, line_num_offset)
    ltype = ltype_from_open_tokens(opens)
    _indent, nesting_level = calc_nesting_depth(opens)
    @prompt.call(ltype, nesting_level, opens.any? || continue, @line_no + line_num_offset)
  end

  # TODO: do not use this. change the api. example: @input.call(prompt)
  def store_prompt_to_irb(opens, continue, line_num_offset)
    prompt(opens, continue, line_num_offset)
  end

  def readmultiline
    if @io.respond_to? :check_termination
      store_prompt_to_irb([], false, 0)
      @input.call
    else
      # nomultiline
      code = ''
      line_offset = 0
      save_prompt_to_context_io([], false, 0)
      loop do
        l = @input.call
        unless l
          return code.empty? ? nil : code
        end
        code << l
        return code if command?(code)
        check_target_code = code.gsub(/\s*\z/, '').concat("\n")
        tokens = KatakataIrb::RubyLexPatch.complete_tokens(check_target_code, context: @context)
        opens = KatakataIrb::NestingParser.parse(tokens)
        continue = process_continue(tokens)
        return code if opens.empty? && !continue && !check_code_block(check_target_code, tokens)
        line_offset += 1
        save_prompt_to_context_io(opens, continue, line_offset)
      end
    end
  end

  def each_top_level_statement(_context = nil)
    loop do
      begin
        code = readmultiline
        break unless code
        if code != "\n"
          code.force_encoding(@io.encoding)
          yield code, @line_no
        end
        @line_no += code.count("\n")
      rescue RubyLex::TerminateLineInput
      end
    end
  end
end
