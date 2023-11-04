# frozen_string_literal: true

require 'test_helper'
KatakataIrb::Types.preload_in_thread.join

class TestCompletor < Minitest::Test
  def empty_binding() = binding

  def assert_completion(code, binding: empty_binding, include: nil, exclude: nil)
    raise ArgumentError if include.nil? && exclude.nil?
    result = KatakataIrb::Completor.analyze code.strip, binding
    _name, candidates = KatakataIrb::Completor.candidates_from_result result
    assert ([*include] - candidates).empty?, "Expected #{candidates} to include #{include}" if include
    assert (candidates & [*exclude]).empty?, "Expected #{candidates} not to include #{exclude}" if exclude
  end

  def test_require
    assert_completion("require '", include: 'set')
    assert_completion("require 's", include: 'set')
    assert_completion("require_relative 'tes", include: 'test/test_completion')
    # Incomplete double quote string is InterpolatedStringNode
    assert_completion('require "', include: 'set')
    assert_completion('require "s', include: 'set')
  end

  def test_method_block_sym
    assert_completion('[1].map(&:', include: 'abs')
    assert_completion('[:a].map(&:', exclude: 'abs')
    assert_completion('[1].map(&:a', include: 'abs')
  end

  def test_call
    assert_completion('1.', include: 'abs')
    assert_completion('1.a', include: 'abs')
  end

  def test_lvar
    bind = eval('hoge = 1; binding')
    assert_completion('hoge.', binding: bind, include: 'abs')
    assert_completion('hoge.a', binding: bind, include: 'abs')
    assert_completion('hoge = ""; hoge.', binding: bind, include: 'ascii_only?')
    assert_completion('hoge = ""; hoge.', include: 'ascii_only?')
  end

  def test_const
    assert_completion('Ar', include: 'Array')
    assert_completion('::Ar', include: 'Array')
    assert_completion('KatakataIrb::T', include: 'Types')
    assert_completion('FooBar=1; F', include: 'FooBar')
    assert_completion('::FooBar=1; ::F', include: 'FooBar')
    assert_completion('::', include: 'Array')
    assert_completion('class ::', include: 'Array')
    assert_completion('module KatakataIrb; class T', include: ['Types', 'TracePoint'])
  end

  def test_gvar
    assert_completion('$', include: '$stdout')
    assert_completion('$s', include: '$stdout')
    assert_completion('$', exclude: '$foobar')
    assert_completion('$foobar=1; $', include: '$foobar')
  end

  def test_ivar
    bind = Object.new.instance_eval { @hoge = 1; binding }
    assert_completion('@', binding: bind, include: '@hoge')
    assert_completion('@h', binding: bind, include: '@hoge')
    assert_completion('@fuga = 1; @', include: '@fuga')
    assert_completion('@fuga = 1; @f', include: '@fuga')
  end

  @@test_cvar = 1
  def test_cvar
    bind = binding
    assert_completion('@@', binding: bind, include: '@@test_cvar')
    assert_completion('@@t', binding: bind, include: '@@test_cvar')
    assert_completion('@@fuga = 1; @', include: '@@fuga')
    assert_completion('@@fuga = 1; @@', include: '@@fuga')
    assert_completion('@@fuga = 1; @@f', include: '@@fuga')
  end

  def test_basic_object
    bo = BasicObject.new
    def bo.foo; end
    bo.instance_eval { @bar = 1 }
    bind = binding
    assert_completion('bo.f', binding: bind, include: 'foo')
    assert_completion('def bo.baz; self.', binding: bind, include: 'foo')
    assert_completion('def bo.baz; @', binding: bind, include: '@bar')
    assert_completion('def bo.baz; @bar.', binding: bind, include: 'abs')
    bo_self_bind = bo.instance_eval { Kernel.binding }
    assert_completion('@', binding: bo_self_bind, include: '@bar')
    assert_completion('@bar.', binding: bo_self_bind, include: 'abs')
  end
end
