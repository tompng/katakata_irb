require 'test_helper'

class TestTypeAnalyze < Minitest::Test
  def empty_binding() = binding

  def analyze(code, binding: nil)
    KatakataIrb::Completor.analyze(code, binding || empty_binding)
  end

  def assert_analyze_type(code, type, token = nil, binding: empty_binding)
    result_type, result_token = analyze(code, binding:)
    assert_equal type, result_type
    assert_equal token, result_token if token
  end

  def assert_no_log
    original_output = KatakataIrb.log_output
    output = StringIO.new
    KatakataIrb.log_output = output
    yield
    output.rewind
    assert_empty output.read
  ensure
    KatakataIrb.log_output = original_output
  end

  def assert_call(code, include: nil, exclude: nil, binding: nil)
    raise ArgumetError if include.nil? && exclude.nil?
    analyze(code, binding:) => [:call, type,]
    klasses = type.types.flat_map do
      _1.klass.singleton_class? ? [_1.klass.superclass, _1.klass] : _1.klass
    end
    assert ([*include] - klasses).empty?, "Expected #{klasses} to include #{include}" if include
    assert (klasses & [*exclude]).empty?, "Expected #{klasses} not to include #{exclude}" if exclude
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

  def test_rescue_assign_no_log
    assert_no_log do
      assert_nil analyze('begin; rescue => a')
      assert_equal [:gvar, '$a'], analyze('begin; rescue => $a')
      assert_equal [:ivar, '@a'], analyze('begin; rescue => @a')
      assert_equal [:cvar, '@@a'], analyze('begin; rescue => @@a')
      # Do not complete assigning to non-variable in rescue
      assert_nil analyze('begin; rescue => A')
      assert_nil analyze('begin; rescue => (a).b')
      assert_nil analyze('begin; rescue => (a)::b')
      assert_nil analyze('begin; rescue => (a)::A')
      assert_nil analyze('begin; rescue => (a).A')
    end
  end

  def test_ref
    lvar = 1
    bind = Class.new do
      instance_variable_set(:@ivar, :a)
      class_variable_set(:@@cvar, 'a')
      break binding
    end
    assert_call('STDIN.', include: STDIN.singleton_class)
    assert_call('$stdin.', include: $stdin.singleton_class)
    assert_call('lvar.', include: lvar.class, binding: bind)
    assert_call('@ivar.', include: Symbol, binding: bind)
    assert_call('@@cvar.', include: String, binding: bind)
  end

  def test_sig_dir
    assert_call('KatakataIrb::Completor.analyze("").', include: [NilClass, Array], exclude: Object)
    assert_call('KatakataIrb::Completor.analyze("")[rand(4)].', include: [Symbol, Object, String, TrueClass, FalseClass], exclude: NilClass)
    assert_call('KatakataIrb::Completor.setup.', include: Object, exclude: NilClass)
  end

  def test_lvar_singleton_method
    a = 1
    b = ''
    c = Object.new
    d = [a, b, c]
    binding = Kernel.binding
    assert_call('a.', include: Integer, exclude: String, binding:)
    assert_call('b.', include: b.singleton_class, exclude: [Integer, Object], binding:)
    assert_call('c.', include: c.singleton_class, exclude: [Integer, String], binding:)
    assert_call('d.', include: d.class, exclude: [Integer, String, Object], binding:)
    assert_call('d.sample.', include: [Integer, String, Object], exclude: [b.singleton_class, c.singleton_class], binding:)
  end

  def test_local_variable_assign
    assert_call('a = 1; a = ""; a.', include: String, exclude: Integer)
    assert_call('1 => a; a.', include: Integer)
  end

  def test_block_symbol
    assert_call('1.times.map(&:', include: Integer)
    assert_call('1.to_s.tap(&:', include: String)
  end

  def test_union_splat
    assert_call('a, = [[:a], 1, nil].sample; a.', include: [Symbol, Integer, NilClass], exclude: Object)
    assert_call('[[:a], 1, nil].each do _2; _1.', include: [Symbol, Integer, NilClass], exclude: Object)
    assert_call('a = [[:a], 1, nil, ("a".."b")].sample; [*a].sample.', include: [Symbol, Integer, NilClass, String], exclude: Object)
  end

  def test_range
    assert_call('(1..2).first.', include: Integer)
    assert_call('("a".."b").first.', include: String)
    assert_call('(..1.to_f).first.', include: Float)
    assert_call('(1.to_s..).first.', include: String)
    assert_call('(1..2.0).first.', include: [Float, Integer])
  end

  def test_conditional_assign
    assert_call('a = 1; a = "" if cond; a.', include: [String, Integer], exclude: NilClass)
    assert_call('a = 1 if cond; a.', include: [Integer, NilClass])
    assert_call(<<~RUBY, include: [String, Symbol], exclude: [Integer, NilClass])
      a = 1
      cond ? a = '' : a = :a
      a.
    RUBY
  end

  def test_block_break
    assert_call('1.tap{}.', include: [Integer], exclude: NilClass)
    assert_call('1.tap{break :a; break "a"}.', include: [Symbol, Integer], exclude: [NilClass, String])
    assert_call('1.tap{break :a if b}.', include: [Symbol, Integer], exclude: NilClass)
    assert_call('1.tap{break :a; break "a" if b}.', include: [Symbol, Integer], exclude: [NilClass, String])
    assert_call('1.tap{if cond; break :a; else; break "a"; end}.', include: [Symbol, Integer, String], exclude: NilClass)
  end

  def test_instance_eval
    assert_call('1.instance_eval{:a.then{self.', include: Integer, exclude: Symbol)
    assert_call('1.then{:a.instance_eval{self.', include: Symbol, exclude: Integer)
  end

  def test_block_next
    assert_call('nil.then{1}.', include: Integer, exclude: [NilClass, Object])
    assert_call('nil.then{next 1; 1.0}.', include: Integer, exclude: [Float, NilClass, Object])
    assert_call('nil.then{next 1; next 1.0}.', include: Integer, exclude: [Float, NilClass, Object])
    assert_call('nil.then{1 if cond}.', include: [Integer, NilClass], exclude: Object)
    assert_call('nil.then{if cond; 1; else; 1.0; end}.', include: [Integer, Float], exclude: [NilClass, Object])
    assert_call('nil.then{next 1 if cond; 1.0}.', include: [Integer, Float], exclude: [NilClass, Object])
    assert_call('nil.then{if cond; next 1; else; next 1.0; end; "a"}.', include: [Integer, Float], exclude: [String, NilClass, Object])
    assert_call('nil.then{if cond; next 1; else; next 1.0; end; next "a"}.', include: [Integer, Float], exclude: [String, NilClass, Object])
  end

  def test_vars_with_branch_termination
    assert_call('a=1; tap{break; a=//}; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; tap{a=1.0; break; a=//}; a.', include: [Integer, Float], exclude: Regexp)
    assert_call('a=1; tap{next; a=//}; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; tap{a=1.0; next; a=//}; a.', include: [Integer, Float], exclude: Regexp)
    assert_call('a=1; while cond; break; a=//; end; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; while cond; a=1.0; break; a=//; end; a.', include: [Integer, Float], exclude: Regexp)
    assert_call('a=1; ->{ break; a=// }; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; ->{ a=1.0; break; a=// }; a.', include: [Integer, Float], exclude: Regexp)

    assert_call('a=1; tap{ break; a=// if cond }; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; tap{ next; a=// if cond }; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; while cond; break; a=// if cond; end; a.', include: Integer, exclude: Regexp)
    assert_call('a=1; ->{ break; a=// if cond }; a.', include: Integer, exclude: Regexp)

    assert_call('a=1; tap{if cond; a=:a; break; a=""; end; a.', include: Integer, exclude: [Symbol, String])
    assert_call('a=1; tap{if cond; a=:a; break; a=""; end; a=//}; a.', include: [Integer, Symbol, Regexp], exclude: String)
    assert_call('a=1; tap{if cond; a=:a; break; a=""; else; break; end; a=//}; a.', include: [Integer, Symbol], exclude: [String, Regexp])
    assert_call('a=1; tap{if cond; a=:a; next; a=""; end; a.', include: Integer, exclude: [Symbol, String])
    assert_call('a=1; tap{if cond; a=:a; next; a=""; end; a=//}; a.', include: [Integer, Symbol, Regexp], exclude: String)
    assert_call('a=1; tap{if cond; a=:a; next; a=""; else; next; end; a=//}; a.', include: [Integer, Symbol], exclude: [String, Regexp])
    assert_call('def f(a=1); if cond; a=:a; return; a=""; end; a.', include: Integer, exclude: [Symbol, String])
    assert_call('a=1; while cond; if cond; a=:a; break; a=""; end; a.', include: Integer, exclude: [Symbol, String])
    assert_call('a=1; while cond; if cond; a=:a; break; a=""; end; a=//; end; a.', include: [Integer, Symbol, Regexp], exclude: String)
    assert_call('a=1; while cond; if cond; a=:a; break; a=""; else; break; end; a=//; end; a.', include: [Integer, Symbol], exclude: [String, Regexp])
    assert_call('a=1; ->{ if cond; a=:a; break; a=""; end; a.', include: Integer, exclude: [Symbol, String])
    assert_call('a=1; ->{ if cond; a=:a; break; a=""; end; a=// }; a.', include: [Integer, Symbol, Regexp], exclude: String)
    assert_call('a=1; ->{ if cond; a=:a; break; a=""; else; break; end; a=// }; a.', include: [Integer, Symbol], exclude: [String, Regexp])

    # continue simulation on terminated branch
    assert_call('a=1; tap{ a=1.0; break; a=// if cond; a.', include: [Regexp, Float], exclude: Integer)
    assert_call('a=1; tap{ a=1.0; next; a=// if cond; a.', include: [Regexp, Float], exclude: Integer)
    assert_call('a=1; ->{ a=1.0; break; a=// if cond; a.', include: [Regexp, Float], exclude: Integer)
    assert_call('a=1; while cond; a=1.0; break; a=// if cond; a.', include: [Regexp, Float], exclude: Integer)
  end

  def test_to_str_to_int
    sobj = Data.define(:to_str).new('a')
    iobj = Data.define(:to_int).new(1)
    binding = Kernel.binding
    assert_equal String, ([] * sobj).class
    assert_equal Array, ([] * iobj).class
    assert_call('([]*sobj).', include: String, exclude: Array, binding:)
    assert_call('([]*iobj).', include: Array, exclude: String, binding:)
  end

  def test_method_select
    assert_call('([]*4).', include: Array, exclude: String)
    assert_call('([]*"").', include: String, exclude: Array)
    assert_call('([]*unknown).', include: [String, Array])
    assert_call('p(1).', include: Integer)
    assert_call('p(1, 2).', include: Array, exclude: Integer)
  end

  def test_interface_match_var
    assert_call('([1]+[:a]+["a"]).sample.', include: [Integer, String, Symbol])
  end

  def test_lvar_scope
    code = <<~RUBY
      tap { a = :never }
      a = 1 if x?
      tap {|a| a = :never }
      tap { a = 'maybe' }
      a = {} if x?
      a.
    RUBY
    assert_call(code, include: [Hash, Integer, String], exclude: [Symbol])
  end

  def test_lvar_scope_complex
    assert_call('if cond; a = 1; else; tap { a = :a }; end; a.', include: [NilClass, Integer, Symbol], exclude: [Object])
    assert_call('def f; if cond; a = 1; return; end; tap { a = :a }; a.', include: [NilClass, Symbol], exclude: [Integer, Object])
    assert_call('def f; if cond; return; a = 1; end; tap { a = :a }; a.', include: [NilClass, Symbol], exclude: [Integer, Object])
    assert_call('def f; if cond; return; if cond; return; a = 1; end; end; tap { a = :a }; a.', include: [NilClass, Symbol], exclude: [Integer, Object])
    assert_call('def f; if cond; return; if cond; return; a = 1; end; end; tap { a = :a }; a.', include: [NilClass, Symbol], exclude: [Integer, Object])
  end

  def test_gvar_no_scope
    code = <<~RUBY
      tap { $a = :maybe }
      $a = 'maybe' if x?
      $a.
    RUBY
    assert_call(code, include: [Symbol, String])
  end

  def test_ivar_no_scope
    code = <<~RUBY
      tap { @a = :maybe }
      @a = 'maybe' if x?
      @a.
    RUBY
    assert_call(code, include: [Symbol, String])
  end

  def test_massign
    assert_call('a,=[1,2]; a.', include: Integer, exclude: Array)
    assert_call('a,b=[1,2]; a.', include: Integer, exclude: Array)
    assert_call('a,b=[1,2]; b.', include: Integer, exclude: Array)
    assert_call('a,*,b=[1,2]; a.', include: Integer, exclude: Array)
    assert_call('a,*,b=[1,2]; b.', include: Integer, exclude: Array)
    assert_call('a,*b=[1,2]; a.', include: Integer, exclude: Array)
    assert_call('a,*b=[1,2]; b.', include: Array, exclude: Integer)
    assert_call('a,*b=[1,2]; b.sample.', include: Integer)
    assert_call('*a=[1,2]; a.', include: Array, exclude: Integer)
    assert_call('*a=[1,2]; a.sample.', include: Integer)
    assert_call('a,*b,c=[1,2,3]; b.', include: Array, exclude: Integer)
    assert_call('a,*b,c=[1,2,3]; b.sample.', include: Integer)
    assert_call('a,b=(cond)?[1,2]:[:a,:b]; a.', include: [Integer, Symbol])
    assert_call('a,b=(cond)?[1,2]:[:a,:b]; b.', include: [Integer, Symbol])
    assert_call('a,b=(cond)?[1,2]:"s"; a.', include: [Integer, String])
    assert_call('a,b=(cond)?[1,2]:"s"; b.', include: Integer, exclude: String)
    assert_call('a,*b=(cond)?[1,2]:"s"; a.', include: [Integer, String])
    assert_call('a,*b=(cond)?[1,2]:"s"; b.', include: Array, exclude: [Integer, String])
    assert_call('a,*b=(cond)?[1,2]:"s"; b.sample.', include: Integer, exclude: String)
    assert_call('*a=(cond)?[1,2]:"s"; a.', include: Array, exclude: [Integer, String])
    assert_call('*a=(cond)?[1,2]:"s"; a.sample.', include: [Integer, String])
    assert_call('a,(b,),c=[1,[:a],4]; b.', include: Symbol)
  end

  def test_defined
    assert_call('defined?(a.b+c).', include: [String, NilClass])
    assert_call('defined?(a = 1); tap { a = 1.0 }; a.', include: [Integer, Float, NilClass])
  end

  def test_ternary_operator
    assert_call('condition ? 1.chr.', include: [String])
    assert_call('condition ? value : 1.chr.', include: [String])
    assert_call('condition ? cond ? cond ? value : cond ? value : 1.chr.', include: [String])
  end

  def test_block_parameter
    assert_call('method { |arg = 1.chr.', include: [String])
    assert_call('method do |arg = 1.chr.', include: [String])
    assert_call('method { |arg1 = 1.|(2|3), arg2 = 1.chr.', include: [String])
    assert_call('method do |arg1 = 1.|(2|3), arg2 = 1.chr.', include: [String])
  end

  def test_self
    integer_binding = 1.instance_eval { Kernel.binding }
    assert_call('self.', include: [Integer], binding: integer_binding)
    string = ''
    string_binding = string.instance_eval { Kernel.binding }
    assert_call('self.', include: [string.singleton_class], binding: string_binding)
    object = Object.new
    object.instance_eval { @int = 1; @string = string }
    object_binding = object.instance_eval { Kernel.binding }
    assert_call('self.', include: [object.singleton_class], binding: object_binding)
    assert_call('@int.', include: [Integer], binding: object_binding)
    assert_call('@string.', include: [String], binding: object_binding)
  end

  def test_optional_chain
    assert_call('[1,nil].sample.', include: [Integer, NilClass])
    assert_call('[1,nil].sample.chr.', include: [String], exclude: [NilClass])
    assert_call('[1,nil].sample&.chr.', include: [String, NilClass])
    assert_call('[1,nil].sample.chr&.ord.', include: [Integer], exclude: [NilClass])
    assert_call('a = 1; b.c(a = :a); a.', include: [Symbol], exclude: [Integer])
    assert_call('a = 1; b&.c(a = :a); a.', include: [Integer, Symbol])
  end

  def test_command_call_arg
    assert_call('[1][0..].', include: [Array, NilClass], exclude: Integer)
    assert_call('[1][rand 1].', include: Integer, exclude: [Array, NilClass])
    assert_call('[1].[](rand 1).', include: Integer, exclude: [Array, NilClass])
    assert_call('[1].[](rand 1){}.', include: Integer, exclude: [Array, NilClass])
    assert_call('[1][1.+ 2].', include: Integer, exclude: [Array, NilClass])
    assert_call('[1].[](1.+ 2).', include: Integer, exclude: [Array, NilClass])
    assert_call('[1].[](1.+ 2){}.', include: Integer, exclude: [Array, NilClass])
  end
end
