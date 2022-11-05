PATCHED_IRB_RELINE_PATH = File.expand_path "~/Documents/github/ruby"
if Dir.exist? PATCHED_IRB_RELINE_PATH
  Kernel.prepend Module.new {
    def require(name)
      if name =~ /^(irb|reline)(\/|$)/
        name = PATCHED_IRB_RELINE_PATH + "/#$1/lib/" + name
      end
      super(name)
    end
  }
end

require 'irb'
require_relative './ruby_lex_patch'
require_relative './completion'
(RubyLex.instance_methods(false) - [:initialize_input, :set_prompt]).each { RubyLex.remove_method _1 }
RubyLex.prepend RubyLexPatch
Completion.patch_to_completor
IRB.start(__FILE__)
