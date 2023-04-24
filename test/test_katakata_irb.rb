# frozen_string_literal: true
require 'test_helper'

class TestKatakataIrb < Minitest::Test
  def test_analyze_does_not_raise_error
    KatakataIrb::TypeSimulator::DigTarget.prepend(
      Module.new do
        def dig?(*) = true
      end
    )
    KatakataIrb.singleton_class.prepend(
      Module.new do
        def log_puts(*)
          raise 'Unexpected log output in test'
        end
      end
    )
    Dir.glob '**/*.rb' do |file|
      assert KatakataIrb::Completor.analyze("(\n#{File.read(file)}\n).hoge"), "analyzing #{file}"
    end
    syntax_ok = !!Ripper.sexp(SYNTAX_TEST_CODE)
    assert syntax_ok if RUBY_VERSION > '3.1'
    assert KatakataIrb::Completor.analyze("(#{SYNTAX_TEST_CODE}).hoge"), "analyzing SYNTAX_TEST_CODE"
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
