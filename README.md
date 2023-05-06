# KatakataIrb: IRB with Kata(型 Type) completion

KatakataIrb might provide a better autocompletion based on type analysis to irb.

## Installation

```
gem install katakata_irb
```
## Usage

Just require katakata_irb or write it to your `.irbrc` file.

```ruby
# .irbrc
require 'katakata_irb' rescue nil
```

```
irb(main):001:0> require 'katakata_irb'
=> true
irb(main):002:0> [1,'a'].sample.a█
                |[1,'a'].sample.abs        |
                |[1,'a'].sample.abs2       |
                |[1,'a'].sample.allbits?   |
                |[1,'a'].sample.angle      |
                |[1,'a'].sample.anybits?   |
                |[1,'a'].sample.arg        |
                |[1,'a'].sample.ascii_only?|
```

```
irb(main):001:0> require 'katakata_irb'
=> true
irb(main):002:0> a = 10
=> 10
irb(main):003:1* if true
irb(main):004:2*   b = a.times.map do
irb(main):005:2*     _1.to_s
irb(main):006:1*   end
irb(main):007:1*   b[0].a█
                  |b[0].ascii_only?|
```
