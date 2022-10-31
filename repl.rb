PATCHED_IRB_RELINE_PATH = File.expand_path "~/Documents/github/ruby"
if Dir.exist? PATCHED_IRB_RELINE_PATH
  Kernel.prepend Module.new {
    def require(name)
      if name =~ /^(irb|reline)(\/|$)/
        name = PATCHED_IRB_RELINE_PATH + "/#$1/lib/" + name
      end
      super(name)
    end
  }
end

require 'irb'
require_relative './trex'

$logfile = File.open 'output.log', 'w'
def log(*args)
  args.each{$logfile.puts _1.inspect }
  $logfile.flush
end

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

  def process_nesting_level(tokens = @tokens)
    opens, heredocs = TRex.parse(tokens){}
    _indent, nesting = calc_nesting_depth opens.map(&:first) + heredocs
    nesting
  end

  def process_indent_level(tokens = @tokens)
    opens, heredocs = TRex.parse(tokens){}
    indent, _nesting = calc_nesting_depth(opens.map(&:first) + heredocs)
    indent * 2
  end

  def check_corresponding_token_depth(_lines, line_index)
    lines, = TRex.parse_line(@tokens)
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

  def process_continue(tokens)
    tokens.last&.event == :on_sp && tokens.last.tok == "\\\n"
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

  def set_auto_indent(context)
    if @io.respond_to?(:auto_indent) and context.auto_indent_mode
      @io.auto_indent do |lines, line_index, byte_pointer, is_newline|
        if is_newline
          @tokens = self.class.ripper_lex_without_warning(lines[0..line_index].join("\n"), context: context)
          process_indent_level(@tokens)
        else
          code = line_index.zero? ? '' : lines[0..(line_index - 1)].map{ |l| l + "\n" }.join
          last_line = lines[line_index]&.byteslice(0, byte_pointer)
          code += last_line if last_line
          @tokens = self.class.ripper_lex_without_warning(code, context: context)
          check_corresponding_token_depth(lines, line_index)
        end
      end
    end
  end
end

RubyLex.prepend RubyLexPatch
IRB.start(__FILE__)
