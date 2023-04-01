require 'test_helper'

class TestTypeAnalyzeIrb < Minitest::Test
  def empty_binding() = binding

  def analyze(code, binding: nil)
    KatakataIrb::Completor.analyze(code, binding || empty_binding)
  end

  def assert_analyze_type(code, type, token = nil, binding: empty_binding)
    result_type, result_token = analyze(code, binding:)
    assert_equal type, result_type
    assert_equal token, result_token if token
  end

  def assert_call(code, include: nil, exclude: nil, binding: nil)
    raise ArgumetError if include.nil? && exclude.nil?
    analyze(code, binding:) => [:call, type,]
    klasses = type.types.map { _1.klass }
    assert_empty [*include] - klasses if include
    assert_empty klasses & [*exclude] if exclude
  end

  def test_lvar_ivar_gvar_cvar
    assert_analyze_type('puts(x', :lvar_or_method, 'x')
    assert_analyze_type('puts($', :gvar, '$')
    assert_analyze_type('puts($x', :gvar, '$x')
    assert_analyze_type('puts(@', :ivar, '@')
    assert_analyze_type('puts(@x', :ivar, '@x')
    assert_analyze_type('puts(@@', :cvar, '@@')
    assert_analyze_type('puts(@@x', :cvar, '@@x')
  end

  def test_lvar_singleton_method
    a = 1
    b = ''
    c = Object.new
    d = [b, c]
    def b.foo() = 1
    def c.bar() = 1
    binding = Kernel.binding
    assert_call('a.', include: Integer, exclude: String, binding:)
    assert_call('b.', include: b.singleton_class, exclude: Integer, binding:)
    assert_call('c.', include: c.singleton_class, exclude: Integer, binding:)
    assert_call('d.sample.', include: [String, Object], exclude: [b.singleton_class, c.singleton_class], binding:)
  end

  def test_local_variable_assign
    assert_call('a = 1; a = ""; a.', include: String, exclude: Integer)
    assert_call('1 => a; a.', include: Integer)
  end

  def test_block_symbol
    assert_call('1.times.map(&:', include: Integer)
    assert_call('1.to_s.tap(&:', include: String)
  end

  def test_conditional_assign
    assert_call('a = 1; a = "" if cond; a.', include: [String, Integer])
    assert_call(<<~RUBY, include: [String, Symbol], exclude: Integer)
      a = 1
      cond ? a = '' : a = :a
      a.
    RUBY
  end

  def test_to_str_to_int
    sobj = Data.define(:to_str).new('a')
    iobj = Data.define(:to_int).new(1)
    binding = Kernel.binding
    assert_call('([]*sobj).', include: String, exclude: Array, binding:)
    assert_call('([]*iobj).', include: Array, exclude: String, binding:)
  end

  def test_interface_match_var
    assert_call('([1]+[:a]+["a"]).sample.', include: [Integer, String, Symbol])
  end
end
