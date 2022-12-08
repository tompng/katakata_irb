PATCHED_RELINE_PATH = File.expand_path "~/Documents/github/ruby/reline"
if Dir.exist? PATCHED_RELINE_PATH
  Kernel.prepend Module.new {
    def require(name)
      if name =~ /^reline(\/|$)/
        name = PATCHED_RELINE_PATH + '/lib/' + name
      end
      super(name)
    end
  }
end

require 'irb'
require_relative 'ruby_lex_patch'
require_relative 'completion/completor.rb'

RubyLexPatch.patch_to_ruby_lex
Completion::Completor.patch_to_completor
IRB.conf[:USE_RELINE] = false if ARGV.include? '--nomultiline'
IRB.start(__FILE__)
