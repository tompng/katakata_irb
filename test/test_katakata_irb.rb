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

    assert Ripper.sexp(SYNTAX_TEST_CODE)
    assert KatakataIrb::Completor.analyze("(#{SYNTAX_TEST_CODE}).hoge"), 'analyzing SYNTAX_TEST_CODE'

    if RUBY_VERSION >= '3.1'
      assert Ripper.sexp(SYNTAX_TEST_CODE_3_1_PLUS)
      assert KatakataIrb::Completor.analyze("(#{SYNTAX_TEST_CODE_3_1_PLUS}).hoge"), 'analyzing SYNTAX_TEST_CODE_3_1_PLUS'
    end

    # Should analyze whole code in this repository
    files = Dir.glob('lib/**/*.rb') + Dir.glob('test/**/*.rb')
    files.each do |file|
      result = KatakataIrb::Completor.analyze("(\n#{File.read(file)}\n).hoge") rescue nil
      assert result, "analyzing #{file}"
    end
  ensure
    KatakataIrb.log_output = original_output
    KatakataIrb::TypeSimulator::DigTarget.class_eval do
      undef_method :dig?
      alias_method :dig?, :original_dig?
    end
  end

  def test_irb_input_completor_compatibility
    completion = IRB::InputCompletor.retrieve_completion_data 'at_exi', bind: binding, doc_namespace: false
    assert_equal ['at_exit'], completion

    KatakataIrb::Completor.prev_analyze_result = KatakataIrb::Completor.analyze 'a = 1.to_c; a.abs', binding
    document = IRB::InputCompletor.retrieve_completion_data 'a.abs', bind: binding, doc_namespace: true
    assert_equal 'Complex#abs', document
  end

  def completion_candidates(code, binding)
    name, candidates = KatakataIrb::Completor.calculate_candidates(code, binding)
    candidates.map(&:to_s).select { _1.start_with? name }.sort
  end

  def test_const_completion
    old_context = IRB.conf[:MAIN_CONTEXT]
    bind = eval 'class ::Encoding; binding; end'
    assert_equal ['ASCII_8BIT'], completion_candidates('ASCII_8BI', bind)
    assert_equal ['Encoding', 'EncodingError'], completion_candidates('Encodin', bind)
    assert_equal ['Array'], completion_candidates('Arra', bind)
    # TODO: `class A; class B::C; XYZ` to complete A::B::C::XYZ, A::XYZ and XYZ

    IRB.conf[:MAIN_CONTEXT] = Struct.new(:workspace).new(Struct.new(:binding).new(bind))
    KatakataIrb::Completor.prev_analyze_result = KatakataIrb::Completor.analyze 'ABC', bind
    assert_equal 'Encoding', IRB::InputCompletor.retrieve_completion_data('Encoding', bind: bind, doc_namespace: true)
    assert_equal 'Encoding::ASCII_8BIT', IRB::InputCompletor.retrieve_completion_data('ASCII_8BIT', bind: bind, doc_namespace: true)
    assert_equal 'Array', IRB::InputCompletor.retrieve_completion_data('Array', bind: bind, doc_namespace: true)
  ensure
    IRB.conf[:MAIN_CONTEXT] = old_context
  end


  SYNTAX_TEST_CODE_3_1_PLUS = <<~'RUBY'
    def f(*,**,&)
      f(&)
    end
  RUBY

  SYNTAX_TEST_CODE = <<~'RUBY'
    a[i], b[j, k], *, c.d = value
    for a[i], b[j, k], *, c.d in array
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
    case
    when cond
    else
    end
  RUBY
end
