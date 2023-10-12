# frozen_string_literal: true

require_relative "lib/katakata_irb/version"

Gem::Specification.new do |spec|
  spec.name = "katakata_irb"
  spec.version = KatakataIrb::VERSION
  spec.authors = ["tompng"]
  spec.email = ["tomoyapenguin@gmail.com"]

  spec.summary = "IRB with Typed Completion"
  spec.description = "IRB with Typed Completion"
  spec.homepage = "http://github.com/tompng/katakata_irb"
  spec.license = "MIT"
  spec.required_ruby_version = ">= 3.0.0" # recommend >= 3.1.0

  spec.metadata["homepage_uri"] = spec.homepage
  spec.metadata["source_code_uri"] = "http://github.com/tompng/katakata_irb"

  # Specify which files should be added to the gem when it is released.
  # The `git ls-files -z` loads the files in the RubyGem that have been added into git.
  spec.files = Dir.chdir(File.expand_path(__dir__)) do
    `git ls-files -z`.split("\x0").reject do |f|
      (f == __FILE__) || f.match(%r{\A(?:(?:test|spec|features)/|\.(?:git|travis|circleci)|appveyor)})
    end
  end
  spec.bindir = "exe"
  spec.executables = spec.files.grep(%r{\Aexe/}) { |f| File.basename(f) }
  spec.require_paths = ["lib"]

  # Uncomment to register a new dependency of your gem
  spec.add_dependency 'irb', '>= 1.4.0'
  spec.add_dependency 'reline', '>= 0.3.0'
  spec.add_dependency 'yarp', '>= 0.12.0'
  spec.add_dependency 'rbs'

  # For more information and examples about making a new gem, check out our
  # guide at: https://bundler.io/guides/creating_gem.html
end
