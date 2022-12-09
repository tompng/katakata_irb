# KatakataIrb: IRB with Kata(型 Type) completion

KatakataIrb might provide a better autocompletion based on type analysis to irb.

## Installation

```
gem install katakata_irb (not published yet)
```
## Usage

```
% kirb
irb(main):001:0> [1,'a'].sample.a█
                |[1,'a'].sample.abs        |
                |[1,'a'].sample.abs2       |
                |[1,'a'].sample.allbits?   |
                |[1,'a'].sample.angle      |
                |[1,'a'].sample.anybits?   |
                |[1,'a'].sample.arg        |
                |[1,'a'].sample.ascii_only?|
```

```
% kirb
irb(main):001:0> a = 10
=> 10
irb(main):002:1* if true
irb(main):003:2*   b = a.times.map do
irb(main):004:2*     _1.to_s
irb(main):005:1*   end
irb(main):006:1*   b[0].a█
                  |b[0].ascii_only?|
```

```ruby
require 'katakata_irb/completor'
KatakataIrb::Completor.setup
10.times do |i|
  binding.irb
end
```

## Options

### `kirb --debug-output`
Show debug output if it meets unimplemented syntax or something

### `kirb --without-patch`
`kirb` will apply some patches to reline and irb/ruby-lex.rb by default. This option will disable it.
See `lib/katakata_irb/ruby_lex_patch.rb` and `lib/katakata_irb/reline_patches/*.patch`
