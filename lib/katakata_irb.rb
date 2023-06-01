require 'katakata_irb/version'
require 'katakata_irb/completor'
require 'katakata_irb/types'

module KatakataIrb
  class << self
    attr_accessor :log_output, :last_completion_error
    def log_puts(...)
      if STDOUT.tty?
        STDOUT.cooked { log_output&.puts(...) }
      else
        log_output&.puts(...)
      end
    end
  end
end

KatakataIrb::Completor.setup
