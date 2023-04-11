require 'test_helper'

class TestScope < Minitest::Test
  Types = KatakataIrb::Types
  BaseScope = KatakataIrb::BaseScope
  Scope = KatakataIrb::Scope
  NIL = Types::NIL
  A, B, C, D, E, F, G, H, I, J, K = ('A'..'K').map do |name|
    klass = Class.new
    klass.define_singleton_method(:name) { name }
    Types::InstanceType.new(klass)
  end

  def assert_types(expected_types, type)
    assert_equal expected_types.map(&:klass).to_set, type.types.map(&:klass).to_set
  end

  def base_scope
    BaseScope.new(binding, Object.new)
  end

  def test_lvar
    scope = Scope.new base_scope
    scope['a'] = A
    assert_equal A, scope['a']
  end

  def test_conditional
    scope = Scope.new base_scope
    scope.conditional do |sub_scope|
      sub_scope['a'] = A
    end
    assert_types [A, NIL], scope['a']
  end

  def test_branch
    scope = Scope.new base_scope
    scope['c'] = A
    scope['d'] = B
    scope.run_branches(
      -> { _1['a'] = _1['c'] = _1['d'] = C },
      -> { _1['a'] = _1['b'] = _1['d'] = D },
      -> { _1['a'] = _1['b'] = _1['d'] = E },
      -> { _1['a'] = _1['b'] = _1['c'] = _1['d'] = F; _1.terminate }
    )
    assert_types [C, D, E], scope['a']
    assert_types [NIL, D, E], scope['b']
    assert_types [A, C], scope['c']
    assert_types [C, D, E], scope['d']
  end
end
