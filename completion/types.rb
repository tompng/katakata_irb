require 'rbs'
require 'rbs/cli'
module Completion; end
module Completion::Types
  def self.rbs_builder
    @rbs_builder ||= RBS::DefinitionBuilder.new(
      env: RBS::Environment.from_loader(RBS::CLI::LibraryOptions.new.loader).resolve_type_names
    )
  end

  Splat = Struct.new :item

  def self.rbs_search_method(klass, method_name, singleton)
    klass.ancestors.each do |ancestor|
      next unless ancestor.name
      type_name = RBS::TypeName(ancestor.name).absolute!
      definition = (singleton ? rbs_builder.build_singleton(type_name) : rbs_builder.build_instance(type_name)) rescue nil
      method = definition&.methods&.[](method_name)
      return method if definition
    end
    nil
  end

  def self.rbs_methods(type, method_name, args_types, kwargs_type, has_block)
    types = (type in UnionType) ? type.types : [type]
    receivers = types.map do |t|
      case t
      in ProcType
        [t, Proc, false]
      in SingletonType
        [t, t.module_or_class, true]
      in InstanceType
        [t, t.klass, false]
      end
    end
    has_splat = args_types.any? { _1 in Splat }
    methods_with_score = receivers.flat_map do |receiver_type, klass, singleton|
      method = rbs_search_method klass, method_name, singleton
      next [] unless method
      method.method_types.map do |method_type|
        score = 0
        score += 2 if !!method_type.block == has_block
        reqs = method_type.type.required_positionals
        opts = method_type.type.optional_positionals
        rest = method_type.type.rest_positionals
        trailings = method_type.type.trailing_positionals
        keyreqs = method_type.type.required_keywords
        keyopts = method_type.type.optional_keywords
        keyrest = method_type.type.rest_keywords
        args = (kwargs_type && keyreqs.empty? && keyopts.empty? && keyrest.nil?) ? args_types + [kwargs_type] : args_types
        if has_splat
          score += 1 if args.count { !(_1 in Splat) } <= reqs.size + opts.size + trailings.size
        elsif reqs.size + trailings.size <= args.size && (rest || args.size <= reqs.size + opts.size + trailings.size)
          score += 2
          centers = args[reqs.size...-trailings.size]
          given = args.first(reqs.size) + centers.take(opts.size) + args.last(trailings.size)
          expected = (reqs + opts.take(centers.size) + trailings).map(&:type)
          if rest
            given << UnionType[*centers.drop(opts.size)]
            expected << rest.type
          end
          score += given.zip(expected).count do |t, e|
            intersect? t, from_rbs_type(e, receiver_type)
          end
        end
        [[method_type, given || [], expected || []], score]
      end
    end
    max_score = methods_with_score.map(&:last).max
    methods_with_score.select { _2 == max_score }.map(&:first)
  end

  def self.intersect?(a, b)
    atypes = ((a in UnionType) ? a.types : [a]).group_by(&:class)
    btypes = ((b in UnionType) ? b.types : [b]).group_by(&:class)
    intersect = ->(type, &block) do
      aa, bb = [atypes, btypes].map {|types| (types[type] || []).map(&block) }
      (aa & bb).any?
    end
    return true if atypes[ProcType] && btypes[ProcType]
    return true if intersect.call(SingletonType, &:module_or_class)
    intersect.call(InstanceType, &:klass)
  end

  def self.rbs_method_response(receiver_type, method_name, args_types, kwargs_type, has_block)
    methods = rbs_methods(receiver_type, method_name, args_types, kwargs_type, has_block)
    types = methods.map do |method,|
      from_rbs_type method.type.return_type, receiver_type
    end
    UnionType[*types]
  end

  def self.type_from_object(object, max_level: 4)
    max_level -= 1
    case object
    when Array
      if max_level > 0
        values = object.map { type_from_object(_1, max_level:) }
        InstanceType.new Array, { Elem: UnionType[*values] }
      else
        InstanceType.new Array, { Elem: UnionType[*object.map(&:class).uniq.map { InstanceType.new _1 }] }
      end
    when Hash
      if max_level > 0
        keys = object.keys.map { type_from_object(_1, max_level:) }
        values = object.values.map { type_from_object(_1, max_level:) }
        InstanceType.new Hash, { K: UnionType[*keys], V: UnionType[*values] }
      else
        keys = object.keys.map(&:class).uniq.map { InstanceType.new _1 }
        values = object.values.map(&:class).uniq.map { InstanceType.new _1 }
        InstanceType.new Hash, { K: UnionType[*keys], V: UnionType[*values] }
      end
    when Module
      SingletonType.new object
    else
      InstanceType.new object.class
    end
  end

  class SingletonType
    attr_reader :module_or_class
    def initialize(module_or_class)
      @module_or_class = module_or_class
    end
    def transform() = yield(self)
    def methods() = @module_or_class.methods
    def all_methods() = methods
    def constants() = @module_or_class.constants
    def types() = [self]
  end

  class InstanceType
    attr_reader :klass, :params
    def initialize(klass, params = {})
      @klass = klass
      @params = params
    end
    def transform() = yield(self)
    def methods() = @klass.instance_methods
    def all_methods() = @klass.instance_methods | @klass.private_instance_methods
    def constants() = []
    def types() = [self]
  end

  class ProcType
    attr_reader :params, :kwparams, :return_type
    def initialize(params = [], kwparams = {}, return_type = NIL)
      @params = params
      @kwparams = kwparams
      @return_type = return_type
    end
    def transform() = yield(self)
    def methods() = Proc.instance_methods
    def all_methods() = Proc.instance_methods | Proc.private_instance_methods
    def constants() = []
    def types() = [self]
  end

  NIL = InstanceType.new NilClass
  OBJECT = InstanceType.new Object
  TRUE = InstanceType.new FalseClass
  FALSE = InstanceType.new FalseClass
  SYMBOL = InstanceType.new Symbol
  STRING = InstanceType.new String
  INTEGER = InstanceType.new Integer
  RANGE = InstanceType.new Range
  REGEXP = InstanceType.new Regexp
  FLOAT = InstanceType.new Float
  RATIONAL = InstanceType.new Rational
  COMPLEX = InstanceType.new Complex
  ARRAY = InstanceType.new Array
  HASH = InstanceType.new Hash
  CLASS = InstanceType.new Class
  MODULE = InstanceType.new Module
  PROC = ProcType.new

  class UnionType
    attr_reader :types

    def initialize(*types)
      @types = []
      singletons = []
      instances = {}
      procs = []
      collect = -> type do
        case type
        in UnionType
          type.types.each(&collect)
        in InstanceType
          params = (instances[type.klass] ||= {})
          type.params.each do |k, v|
            (params[k] ||= []) << v
          end
        in SingletonType
          singletons << type
        in ProcType
          procs << type
        end
      end
      types.each(&collect)
      @types = procs.uniq + singletons.uniq + instances.map do |klass, params|
        InstanceType.new(klass, params.transform_values { |v| UnionType[*v] })
      end
    end

    def transform(&block)
      UnionType[*types.map(&block)]
    end

    def self.[](*types)
      type = new(*types)
      if type.types.empty?
        OBJECT
      elsif type.types.size == 1
        type.types.first
      else
        type
      end
    end

    def methods() = @types.flat_map(&:methods).uniq
    def all_methods() = @types.flat_map(&:all_methods).uniq
    def constants() = @types.flat_map(&:constants).uniq
  end

  def self.from_rbs_type(return_type, self_type, extra_vars = {})
    case return_type
    when RBS::Types::Bases::Self
      self_type
    when RBS::Types::Bases::Void, RBS::Types::Bases::Bottom, RBS::Types::Bases::Nil
      NIL
    when RBS::Types::Bases::Any
      OBJECT
    when RBS::Types::Bases::Class
      self_type.transform do |type|
        case type
        in SingletonType
          InstanceType.new(self_type.module_or_class.is_a?(Class) ? Class : Module)
        in InstanceType
          SingletonType.new type.klass
        end
      end
      UnionType[*types]
    when RBS::Types::Bases::Bool
      UnionType[TRUE, FALSE]
    when RBS::Types::Bases::Instance
      self_type.transform do |type|
        case type
        in SingletonClass
          InstanceType.new type.klass
        in InstanceType
          case type.klass
          in Class
            InstanceType.new Class
          in Module
            InstanceType.new Module
          else
            OBJECT
          end
        end
      end
    when RBS::Types::Union
      UnionType[*return_type.types.flat_map { from_rbs_type _1, self_type, extra_vars }]
    when RBS::Types::Proc
      InstanceType.new Proc
    when RBS::Types::Tuple
      elem = UnionType[*return_type.types.map { from_rbs_type _1, self_type, extra_vars }]
      InstanceType.new Array, Elem: elem
    when RBS::Types::Record
      InstanceType.new Hash, K: SYMBOL, V: OBJECT
    when RBS::Types::Literal
      InstanceType.new return_type.literal.class
    when RBS::Types::Variable
      if extra_vars.key? return_type.name
        extra_vars[return_type.name]
      elsif self_type in InstanceType
        self_type.params[return_type.name] || OBJECT
      elsif self_type in UnionType
        types = self_type.types.filter_map do |t|
          t.params[return_type.name] if t in InstanceType
        end
        UnionType[*types]
      else
        OBJECT
      end
    when RBS::Types::Optional
      UnionType[from_rbs_type(return_type.type, self_type, extra_vars), NIL]
    when RBS::Types::Alias
      case return_type.name.name
      when :int
        INTEGER
      when :boolish
        UnionType[TRUE, FALSE]
      end
    when RBS::Types::Interface
      p return_type
      # unimplemented
      OBJECT
    when RBS::Types::ClassInstance
      klass = Object.const_get(return_type.name.name)
      return OBJECT unless klass in Class
      if return_type.args
        args = return_type.args.map { from_rbs_type _1, self_type, extra_vars }
        names = rbs_builder.build_singleton(return_type.name).type_params
        params = names.map.with_index { [_1, args[_2] || OBJECT] }.to_h
      end
      InstanceType.new(klass, params || {})
    end
  end

  def self.match_free_variables(vars, types, values)
    accumulator = {}
    types.zip(values).each do |t, v|
      _match_free_variable(vars, t, v, accumulator)
    end
    accumulator.transform_values { UnionType[*_1] }
  end

  def self._match_free_variable(vars, rbs_type, value, accumulator)
    case [rbs_type, value]
    in [RBS::Types::Variable,]
      (accumulator[rbs_type.name] ||= []) << value if vars.include? rbs_type.name
    in [RBS::Types::ClassInstance, InstanceType]
      names = rbs_builder.build_singleton(rbs_type.name).type_params
      names.zip(rbs_type.args).each do |name, arg|
        v = value.params[name]
        _match_free_variable vars, arg, v, accumulator if v
      end
    in [RBS::Types::Tuple, InstanceType] if value.klass == Array
      v = value.params[:Elem]
      rbs_type.types.each do |t|
        _match_free_variable vars, t, v
      end
    in [RBS::Types::Record, InstanceType] if value.klass == Hash
    else
    end
  end
end
