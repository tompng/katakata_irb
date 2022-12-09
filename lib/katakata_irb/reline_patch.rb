module KatakataIrb::RelinePatch
  module RelinePatchIseqLoader; end
  def self.require_patched_reline
    # Apply patches of unmerged pull-request to reline
    patches = %w[wholelines escapeseq indent fullwidth raw scrollbar]
    patched = {}
    require 'reline/version.rb' # result of $LOAD_PATH.resolve_feature_path will change after this require
    patches.each do |patch_name|
      patch = File.read File.expand_path("reline_patches/#{patch_name}.patch", File.dirname(__FILE__))
      current_patched = {}
      patch.gsub(/^diff.+\nindex.+$/, '').split(/^--- a(.+)\n\+\+\+ b(.+)\n/).drop(1).each_slice(3) do |file, newfile, diff|
        raise if file != newfile
        _, path = $LOAD_PATH.resolve_feature_path file.sub(%r{^/lib/}, '')
        code = current_patched[path] || patched[path] || File.read(path)
        diff.split(/^@@.+\n/).drop(1).map(&:lines).each do |lines|
          target = lines.reject { _1[0] == '+' }.map { _1[1..] }.join
          replace = lines.reject { _1[0] == '-' }.map { _1[1..] }.join
          raise unless code.include? target
          code.sub! target, replace
        end
        current_patched[path] = code
      end
      patched.update current_patched
    rescue
      puts "Failed to apply katakata_irb/reline_patches/#{patch_name}.patch to reline"
    end

    RelinePatchIseqLoader.define_method :load_iseq do |fname|
      if patched.key? fname
        RubyVM::InstructionSequence.compile patched[fname], fname
      else
        RubyVM::InstructionSequence.compile_file fname
      end
    end
    RubyVM::InstructionSequence.singleton_class.prepend RelinePatchIseqLoader
    require 'reline'
    RelinePatchIseqLoader.undef_method :load_iseq
  end
end
