require 'rbs'
require 'rbs/cli'
module Completion; end
module Completion::Types
  def self.rbs_builder
    @rbs_builder ||= RBS::DefinitionBuilder.new(
      env: RBS::Environment.from_loader(RBS::CLI::LibraryOptions.new.loader).resolve_type_names
    )
  end

  def self.rbs_method_response(klass, method_name, args_types, kwargs_types, kwsplat, has_block)
    singleton = (klass in { class: klass })
    return [klass] if singleton && method_name == :new
    return klass if method_name == :itself
    return [{ class: klass }] if !singleton && method_name == :class
    type_name = RBS::TypeName(klass.name).absolute!
    definition = (singleton ? rbs_builder.build_singleton(type_name) : rbs_builder.build_instance(type_name)) rescue nil
    return [] unless definition
    method = definition.methods[method_name]
    return [] unless method
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
            args_types.zip(reqs + opts).count do |arg_type, type|
              (arg_type & classes_from_rbs_type(type.type, klass)).any?
            end
          ).fdiv args_types.size
        end
      end
      score += 2 if !kwrest && (kwargs_types.keys - (keywords.keys + keyopts.keys)).empty?
      if keywords.any?
        score += keywords.keys.count { kwargs.has_key? _1 }.fdiv keywords.size
      end
      if keywords.any? || keyopts.any?
        score += { **keywords, **keyopts }.count do |key, type|
          arg_type = kwargs_types[key]
          arg_type && (arg_type & classes_from_rbs_type(type.type, klass)).any?
        end.fdinv keywords.size + keyopts.size
      end
      [method_type, score]
    end
    max_score = method_types_with_score.map(&:last).max
    method_types_with_score.select { _2 == max_score }.map(&:first).flat_map do
      classes_from_rbs_type _1.type.return_type, klass
    end
  end

  def self.classes_from_rbs_type(return_type, self_class)
    case return_type
    when RBS::Types::Bases::Self
      [self_class]
    when RBS::Types::Bases::Void, RBS::Types::Bases::Bottom, RBS::Types::Bases::Nil
      [NilClass]
    when RBS::Types::Bases::Any
      [Object]
    when RBS::Types::Bases::Class
      case self_type
      in { class: Class }
        [{ class: Class }]
      in { class: }
        [{ class: Module }]
      else
        [{ class: self_type }]
      end
    when RBS::Types::Bases::Bool
      [TrueClass, FalseClass]
    when RBS::Types::Bases::Instance
      if self_class in { class: klass }
        [klass]
      elsif self_class == Class || self_class == Module
        [self_class]
      else
        [Object]
      end
    when RBS::Types::Union
      return_type.types.flat_map { classes_from_rbs_type _1, self_class }
    when RBS::Types::Proc
      [Proc]
    when RBS::Types::Tuple
      [Array]
    when RBS::Types::Record
      [Hash]
    when RBS::Types::Literal
      [return_type.literal.class]
    when RBS::Types::Variable
      [Object]
    when RBS::Types::Optional
      classes_from_rbs_type(return_type.type, self_class) | [NilClass]
    when RBS::Types::Alias
      case return_type.name.name
      when :int
        [Integer]
      when :boolish
        [TrueClass, FalseClass]
      end
    when RBS::Types::Interface
      [] # unimplemented
    when RBS::Types::ClassInstance
      [Object.const_get(return_type.name.name)]
    end
  end
end
