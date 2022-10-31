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

RubyLex.prepend Module.new {
  def self.compare_diff(name)
    alias_method "patched_#{name}", name
    define_method(name){|*a,**b,&c|
      original = super(*a,**b,&c)
      patched = send("patched_#{name}", *a,**b,&c)
      if original != patched
        # log([:DIFF, name, a, b, c], @tokens&.map(&:tok), [original, patched])
      else
        #log([:OK, name, a, b, c], @tokens&.map(&:tok), [original, patched])
      end
      patched
    }
  end

  def calc_visible_depth(tokens)
    depth = 0
    tokens.each_with_index do |t, index|
      case t.event
      when :on_heredoc_beg
        if tokens[index + 1]&.event != :on_heredoc_beg
          if t.tok.start_with? '<<~'
            depth += 1
          else
            depth = 0
          end
        end
      when :on_tstring_beg, :on_regexp_beg
        depth += 1 if t.tok[0] == '%'
      when :on_embdoc_beg
        depth = 0
      else
        depth += 1
      end
    end
    depth
  end

  compare_diff def check_newline_depth_difference
    lines, = TRex.parse_line(@tokens)
    return 0 if lines.empty?
    _, _, opens, min_depth = lines.last
    calc_visible_depth(opens.map(&:first)) - calc_visible_depth(opens.take(min_depth).map(&:first))
  end

  compare_diff def process_nesting_level(tokens = @tokens)
    opens, heredocs = TRex.parse(tokens){}
    calc_visible_depth opens.map(&:first) + heredocs
  end

  compare_diff def check_corresponding_token_depth(_lines, line_index)
    lines, = TRex.parse_line(@tokens)
    result = lines[line_index]
    return unless result
    _tokens, prev, opens, min_depth = result
    depth = calc_visible_depth(opens.take(min_depth).map(&:first))
    depth * 2 if depth < calc_visible_depth(prev.map(&:first))
  end

  compare_diff def find_prev_spaces(line_index)
    if line_index == 0
      0
    else
      lines, = TRex.parse_line(@tokens)
      _, _, opens, min_depth = lines[line_index - 1]
      opens ? calc_visible_depth(opens.take(min_depth).map(&:first)) * 2 : 0
    end
  end

  compare_diff def check_string_literal(tokens)
    TRex.parse(tokens){}.first.map(&:first).reverse.find do |t, state|
      %i[on_tstring_beg on_regexp_beg on_symbeg on_backtick on_qwords_beg on_words_beg on_qsymbols_beg on_symbols_beg on_heredoc_beg].include? t.event
    end
  end

  compare_diff def check_termination_in_prev_line(code, context: nil)
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
          prev_spaces = find_prev_spaces(line_index)
          depth_difference = check_newline_depth_difference
          depth_difference = 0 if depth_difference < 0
          indent_was = prev_spaces + depth_difference * 2
          indent = 2 * process_nesting_level(@tokens)
          log [:newline, lines[0..line_index].join("\n"), indent, indent_was]
          2 * process_nesting_level(@tokens)
        else
          code = line_index.zero? ? '' : lines[0..(line_index - 1)].map{ |l| l + "\n" }.join
          last_line = lines[line_index]&.byteslice(0, byte_pointer)
          code += last_line if last_line
          @tokens = self.class.ripper_lex_without_warning(code, context: context)
          indent = check_corresponding_token_depth(lines, line_index)
          log [:nonnewline, code, indent]
        end
        indent
      end
    end
  end

}

IRB.start(__FILE__)
