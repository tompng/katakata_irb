require 'katakata_irb/version'
require 'katakata_irb/completor'

module KatakataIrb
  class << self
    attr_accessor :log_output
    def log_puts(...)
      STDOUT.cooked { log_output&.puts(...) }
    end
  end
end

KatakataIrb::Completor.setup
