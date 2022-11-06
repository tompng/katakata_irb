require 'irb'
require_relative 'trex'
require_relative 'ruby_lex_patch'
if ARGV.any?
  input = ARGV.map{ File.read _1 }.join($/)
else
  input = File.read('./trex.rb') + File.read(__FILE__)
end

tokens = RubyLex.ripper_lex_without_warning input.gsub(/\n +/, "\n")

code = ''
rubylex = Class.new{include RubyLexPatch}.new
TRex.parse_line(tokens).first.each do |ltokens, prev_opens, _next_opens, min_depths|
  open_tokens = prev_opens.map(&:first)
  min_depth_level, = rubylex.calc_nesting_depth open_tokens.take(min_depths)
  prev_level, = rubylex.calc_nesting_depth open_tokens
  indent = '  ' * [min_depth_level, prev_level].min # need comparing for heredoc_end
  if ltokens.first&.first&.event == :on_sp
    code << indent + ltokens.drop(1).map(&:last).join
  else
    code << indent + ltokens.map(&:last).join
  end
end
puts "# Indenting Sample"
puts IRB::Color.colorize_code code
