require 'irb'
require_relative './trex'

code = File.read('./trex.rb') + File.read(__FILE__)
tokens = RubyLex.ripper_lex_without_warning code

code = ''
TRex.parse_line(tokens).first.each do |ltokens, prev_opens, _next_opens, min_depths|
  if ltokens.first&.first&.event == :on_sp
    level = prev_opens.take(min_depths).size
    code << ('  ' * level) + ltokens.drop(1).map(&:last).join
  else
    code << ltokens.map(&:last).join
  end
end

puts IRB::Color.colorize_code code
