require 'rbs'
require 'rbs/cli'

module KatakataIrb
  class EnvironmentLoader
    CACHE_FILENAME = 'system.rbs'.freeze

    attr_reader :loader

    def load
      @loader = RBS::CLI::LibraryOptions.new.loader
      @loader.add path: Pathname('sig')
      RBS::DefinitionBuilder.new env: load_env
    end

    def latest_modified_time
      mtimes = []
      loader.each_dir do |source, dir|
        skip_hidden = !source.is_a?(Pathname)
        mtimes << RBS::FileFinder.each_file(dir, skip_hidden: skip_hidden, immediate: true).map { |f| File.mtime(f) }.max
      end
      mtimes.max
    end

    def load_env
      mtime = latest_modified_time
      if cache_path.exist? && cache_path.mtime == mtime
        new_loader = RBS::EnvironmentLoader.new(core_root: nil)
        new_loader.add(path: cache_path)
        RBS::Environment.from_loader(new_loader)
      else
        RBS::Environment.from_loader(loader).resolve_type_names.tap do |env|
          cache_path.parent.mkpath
          cache_path.open('wt') do |f|
            RBS::Writer.new(out: f).write(env.declarations)
          end
          cache_path.utime(mtime, mtime)
        end
      end
    end

    def cache_path
      @cache_path ||= Pathname(ENV['XDG_CACHE_HOME'] || File.expand_path('~/.cache')).join('katakata_irb', CACHE_FILENAME)
    end
  end
end
