require 'irb'
require_relative './trex'

code = File.read('./trex.rb') + File.read(__FILE__)
code.gsub!(/\n +/, "\n")
tokens = RubyLex.ripper_lex_without_warning code

code = ''
TRex.parse_line(tokens).first.each do |ltokens, prev_opens, _next_opens, min_depths|
  level = prev_opens.take(min_depths).size
  indent = '  ' * level
  if ltokens.first&.first&.event == :on_sp
    code << indent + ltokens.drop(1).map(&:last).join
  else
    code << indent + ltokens.map(&:last).join
  end
end
puts "# Indenting Sample"
puts IRB::Color.colorize_code code
