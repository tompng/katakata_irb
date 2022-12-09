module KatakataIrb
  def self.repl
    require 'katakata_irb/completor'
    KatakataIrb::Completor.patch_to_completor
    IRB.start(__FILE__)
  end
end
