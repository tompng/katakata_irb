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
        log([:DIFF, name, a, b, c], @tokens&.map(&:tok), [original, patched])
      else
        #log([:OK, name, a, b, c], @tokens&.map(&:tok), [original, patched])
      end
      patched
    }
  end

  compare_diff def check_newline_depth_difference
    parsed = TRex.parse_line(@tokens)
    a = parsed[-2]&.last || 0
    b = parsed[-1].last
    b - a
  end

  compare_diff def process_nesting_level(tokens = @tokens)
    TRex.parse_line(tokens).last.last
  end

  compare_diff def check_corresponding_token_depth(lines, line_index)
    result = TRex.parse_line(@tokens)[line_index]
    return unless result
    tokens, prev, current, min_depth = result
    min_depth * 2 if min_depth < prev.size
  end
  
  compare_diff def find_prev_spaces(line_index)
    if line_index == 0
      0
    else
      (TRex.parse_line(@tokens)[line_index - 1]&.last || 0) * 2
    end
  end

  compare_diff def check_string_literal(tokens)
    TRex.parse(tokens){}.reverse.find do |t,|
      %i[on_tstring_beg on_regexp_beg on_symbeg on_backtick on_qwords_beg on_words_beg on_qsymbols_beg on_symbols_beg on_heredoc_beg].include? t.event
    end
  end
}

IRB.start(__FILE__)
