require 'irb'
require_relative './trex'

code = File.read __FILE__
tokens = RubyLex.ripper_lex_without_warning code

code = []
nl = true
TRex.parse(tokens){|t,i,opens|
  p [t,i,opens]
  indent_level = opens.size
  if t.tok.include? "\n"
    code << t.tok.sub(/ *\z/, '')
    nl = true
  elsif nl
    if t.tok !~ /\A *\z/
      ot, = opens.last
      indent_level = opens.size - (ot == t ? 1 : 0)
      code << '  '*indent_level if nl
      nl = false
      code << t.tok
    end
  else
    code << t.tok
  end
}

puts IRB::Color.colorize_code code.join

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
