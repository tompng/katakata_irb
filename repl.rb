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
require_relative 'ruby_lex_patch'
require_relative 'completion/completor.rb'

unless RubyLex.respond_to? :generate_local_variables_assign_code
  def RubyLex.generate_local_variables_assign_code(*)
    '_=nil;'
  end
end

RubyLexPatch.patch_to_ruby_lex
Completion::Completor.patch_to_completor
IRB.conf[:USE_RELINE] = false if ARGV.include? '--nomultiline'
IRB.start(__FILE__)
