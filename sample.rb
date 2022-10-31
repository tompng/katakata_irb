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

if false
  def hoge()=1
  def hoge(x=1)=
    1+2+3
  def (
    1+2.times do
      p 1
    end
  ).to_s x=1
    body
  end

  def (
    (<<~A).tap do
        hello
    A
      p _1
    end
  ).to_s x=->{

  }
   hello
  end

  def self.`
  end
  def self.`(x)=1

  def self.` x=1
    1
  end
  
  self.`(
    1+2
  )

  :"hell
  owo#{
    1+2
  }rld
  hello"

  s = <<~A
    hello
  A

  def hoge(
    x
  )
    fuga
  end

end
