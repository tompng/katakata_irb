require 'rbs'
require 'rbs/cli'
module Completion; end
module Completion::Types
  def self.rbs_builder
    @rbs_builder ||= RBS::DefinitionBuilder.new(
      env: RBS::Environment.from_loader(RBS::CLI::LibraryOptions.new.loader).resolve_type_names
    )
  end

  def self.rbs_method_response(type, method_name, args_types, kwargs_types, kwsplat, has_block)
    if type in UnionType
      types = type.types.map do
        rbs_method_response _1, method_name, args_types, kwargs_types, kwsplat, has_block
      end
      return UnionType[*types]
    end
    klass = case type
    in ProcType
      Proc
    in SingletonType
      type.module_or_class
    in InstanceType
      type.klass
    end
    singleton = (type in SingletonType)
    return InstanceType.new klass if singleton && method_name == :new
    return type if method_name == :itself
    return SingletonType.new klass if !singleton && method_name == :class
    type_name = RBS::TypeName(klass.name).absolute!
    definition = (singleton ? rbs_builder.build_singleton(type_name) : rbs_builder.build_instance(type_name)) rescue nil
    return NilType unless definition
    method = definition.methods[method_name]
    return NilType unless method
    has_splat = !args_types.all?
    method_types_with_score = method.method_types.map do |method_type|
      score = 0
      score += 4 if !!method_type.block == has_block
      reqs = method_type.type.required_positionals
      opts = method_type.type.optional_positionals
      keywords = method_type.type.required_keywords
      keyopts = method_type.type.optional_keywords
      kwrest = method_type.type.rest_keywords
      if has_splat # skip type check
        score += 1 if args_types.compact.size <= reqs.size + opts.size
      elsif reqs.size <= args_types.size && args_types.size <= reqs.size + opts.size
        score += 2
        if args_types.size >= 1
          score += (
            args_types.zip(reqs + opts).count do |arg_type, atype|
              (arg_type & from_rbs_type(atype.type, type)).any? rescue true
            end
          ).fdiv args_types.size
        end
      end
      score += 2 if !kwrest && (kwargs_types.keys - (keywords.keys + keyopts.keys)).empty?
      if keywords.any?
        score += keywords.keys.count { kwargs.has_key? _1 }.fdiv keywords.size
      end
      if keywords.any? || keyopts.any?
        score += { **keywords, **keyopts }.count do |key, t|
          arg_type = kwargs_types[key]
          arg_type && (arg_type & from_rbs_type(t.type, type)).any? rescue true
        end.fdiv keywords.size + keyopts.size
      end
      [method_type, score]
    end
    max_score = method_types_with_score.map(&:last).max
    types = method_types_with_score.select { _2 == max_score }.map(&:first).flat_map do
      from_rbs_type _1.type.return_type, type
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
    def constants() = @module_or_class.constants
  end

  class InstanceType
    attr_reader :klass, :params
    def initialize(klass, params = {})
      @klass = klass
      @params = params
    end
    def transform() = yield(self)
    def methods() = @klass.instance_methods
    def constants() = []
  end

  NilType = InstanceType.new NilClass
  ObjectType = InstanceType.new Object

  class ProcType
    attr_reader :params, :kwparams, :return_type
    def initialize(params = [], kwparams = {}, return_type = NilType)
      @params = params
      @kwparams = kwparams
      @return_type = return_type
    end
    def transform() = yield(self)
    def methods() = Proc.instance_methods
    def constants() = []
  end

  class UnionType
    attr_reader :types

    def initialize(*types)
      @types = []
      singletons = []
      instances = {}
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
        end
      end
      types.each(&collect)
      @types = singletons.uniq + instances.map do |klass, params|
        InstanceType.new(klass, params.transform_values { |v| UnionType[*v] })
      end
    end

    def transform(&block)
      UnionType[*types.map(&block)]
    end

    def self.[](*types)
      type = new(*types)
      if type.types.empty?
        ObjectType
      elsif type.types.size == 1
        type.types.first
      else
        type
      end
    end

    def methods() = @types.flat_map(&:methods).uniq
    def constants() = @types.flat_map(&:constants).uniq
  end

  def self.from_rbs_type(return_type, self_type)
    case return_type
    when RBS::Types::Bases::Self
      self_type
    when RBS::Types::Bases::Void, RBS::Types::Bases::Bottom, RBS::Types::Bases::Nil
      NilType
    when RBS::Types::Bases::Any
      ObjectType
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
      UnionType[InstanceType.new(TrueClass), InstanceType.new(FalseClass)]
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
            ObjectType
          end
        end
      end
    when RBS::Types::Union
      UnionType[*return_type.types.flat_map { from_rbs_type _1, self_type }]
    when RBS::Types::Proc
      InstanceType.new Proc
    when RBS::Types::Tuple
      elem = UnionType[*return_type.types.map { from_rbs_type _1, self_type }]
      InstanceType.new Array, Elem: elem
    when RBS::Types::Record
      InstanceType.new Hash
    when RBS::Types::Literal
      InstanceType.new return_type.literal.class
    when RBS::Types::Variable
      if self_type in InstanceType
        self_type.params[return_type.name] || ObjectType
      else
        ObjectType
      end
    when RBS::Types::Optional
      UnionType[from_rbs_type(return_type.type, self_type), NilType]
    when RBS::Types::Alias
      case return_type.name.name
      when :int
        InstanceType.new Integer
      when :boolish
        UnionType[InstanceType.new(TrueClass), InstanceType.new(FalseClass)]
      end
    when RBS::Types::Interface
      p return_type
      # unimplemented
      ObjectType
    when RBS::Types::ClassInstance
      klass = Object.const_get(return_type.name.name)
      return ObjectType unless klass in Class
      $hoge ||= return_type
      if return_type.args
        args = return_type.args.map { from_rbs_type _1, self_type }
        names = rbs_builder.build_singleton(return_type.name).type_params
        params = names.map.with_index { [_1, args[_2] || ObjectType] }.to_h
      end
      InstanceType.new(klass, params || {})
    end
  end
end
