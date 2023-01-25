require 'katakata_irb/version'
require 'katakata_irb/completor'

module KatakataIrb
  def self.log_output=(output)
    @log_output = output
  end

  def self.log_puts(...)
    STDOUT.cooked { @log_output&.puts(...) }
  end
end

KatakataIrb::Completor.setup
