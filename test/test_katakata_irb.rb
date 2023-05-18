# frozen_string_literal: true
require 'test_helper'

# Needed for ruby 3.0 test
Refinement = Object unless defined? Refinement

class TestKatakataIrb < Minitest::Test
  def test_analyze_does_not_raise_error
    original_output = KatakataIrb.log_output
    KatakataIrb::TypeSimulator::DigTarget.class_eval do
      alias_method :original_dig?, :dig?
      def dig?(*) = true
    end
    KatakataIrb.log_output = Object.new.tap do |output|
      def output.puts(*)
        raise 'Unexpected log output in test'
      end
    end
    Dir.glob '**/*.rb' do |file|
      result = KatakataIrb::Completor.analyze("(\n#{File.read(file)}\n).hoge") rescue nil
      assert result, "analyzing #{file}"
    end
    syntax_ok = !!Ripper.sexp(SYNTAX_TEST_CODE)
    if RUBY_VERSION > '3.1'
      assert syntax_ok
      assert KatakataIrb::Completor.analyze("(#{SYNTAX_TEST_CODE}).hoge"), "analyzing SYNTAX_TEST_CODE"
    end
  ensure
    KatakataIrb.log_output = original_output
    KatakataIrb::TypeSimulator::DigTarget.class_eval do
      undef_method :dig?
      alias_method :dig?, :original_dig?
    end
  end

  SYNTAX_TEST_CODE = <<~'RUBY'
    a[i], b[j, k], *, c.d = value
    for a[i], b[j, k], *, c.d in array
    end
    def f(*,**,&)
      f(&)
    end
    def f(...)
      f(...)
    end
    p(?a'b'"c", %(a)"b#{c}d"'e'"f#{g}h")
    p ()
    p (1.method)
    (a,b)=1
    def f() #comment
    =begin
    embdoc
    =end
      = 1
  RUBY
end
