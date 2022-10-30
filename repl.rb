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
end

RubyLex.prepend Module.new {
  def process_nesting_level(tokens = @tokens)
    TRex.each_line(tokens){}.last || 0
  end

  def check_corresponding_token_depth(lines, line_index)
    i = 0
    (TRex.each_line(@tokens) do
      return _4 * 2 if line_index == i
      i += 1
    end.last || 0) * 2
  end
  
  def check_string_literal(tokens)
    TRex.parse(tokens){}.reverse.find do |t,|
      %i[on_tstring_beg on_regexp_beg on_symbeg on_backtick on_qwords_beg on_words_beg on_qsymbols_beg on_symbols_beg on_heredoc_beg].include? t.event
    end
  end
}

IRB.start(__FILE__)
