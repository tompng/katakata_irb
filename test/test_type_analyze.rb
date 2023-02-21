require 'test_helper'

class TestTypeAnalyzeIrb < Minitest::Test
  def empty_binding() = binding

  def analyze(code, binding = empty_binding)
    KatakataIrb::Completor.analyze(code, binding)
  end

  def assert_call(code, include: nil, exclude: nil)
    raise ArgumetError if include.nil? && exclude.nil?
    analyze(code) => [:call, type,]
    klasses = type.types.map { _1.klass }
    assert_empty include - klasses if include
    assert_empty klasses & exclude if exclude
  end

  def test_local_variable_assign
    assert_call('a = 1; a = ""; a.', include: [String], exclude: [Integer])
    assert_call('1 => a; a.', include: [Integer])
  end

  def test_conditional_assign
    assert_call('a = 1; a = "" if cond; a.', include: [String, Integer])
    assert_call(<<~RUBY, include: [String, Symbol], exclude: [Integer])
      a = 1
      cond ? a = '' : a = :a
      a.
    RUBY
  end
end
