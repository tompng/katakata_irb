require 'io/console'
module KatakataIrb
  def self.repl
    require 'katakata_irb/completor'
    KatakataIrb::Completor.setup
    IRB.start(__FILE__)
  end

  def self.log_output=(output)
    @log_output = output
  end

  def self.log_puts(...)
    STDOUT.cooked { @log_output&.puts(...) }
  end
end
