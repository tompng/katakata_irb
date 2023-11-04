# frozen_string_literal: true

require 'set'
require_relative 'types'

module KatakataIrb
  class BaseScope
    BREAK_RESULT = '%break'
    NEXT_RESULT = '%next'
    RETURN_RESULT = '%return'
    PATTERNMATCH_BREAK = '%match'

    OBJECT_SINGLETON_CLASS_METHOD = Object.instance_method(:singleton_class)
    OBJECT_INSTANCE_VARIABLES_METHOD = Object.instance_method(:instance_variables)
    OBJECT_INSTANCE_VARIABLE_GET_METHOD = Object.instance_method(:instance_variable_get)

    attr_reader :module_nesting, :self_object

    def initialize(binding, self_object, local_variables)
      @binding = binding
      @self_object = self_object
      @cache = {}
      modules = [*binding.eval('::Module.nesting'), Object]
      @module_nesting = modules.map { [_1, []] }
      binding_local_variables = binding.local_variables
      uninitialized_locals = local_variables - binding_local_variables
      uninitialized_locals.each { @cache[_1] = KatakataIrb::Types::NIL }
      @local_variables = (local_variables | binding_local_variables).map(&:to_s).to_set
      @global_variables = Kernel.global_variables.map(&:to_s).to_set
      @owned_constants_cache = {}
    end

    def level() = 0

    def level_of(_name, _var_type) = 0

    def mutable?() = false

    def module_own_constant?(mod, name)
      set = (@owned_constants_cache[mod] ||= Set.new(mod.constants.map(&:to_s)))
      set.include? name
    end

    def get_const(nesting, path, _key = nil)
      return unless nesting

      result = path.reduce nesting do |mod, name|
        return nil unless mod.is_a?(Module) && module_own_constant?(mod, name)
        mod.const_get name
      end
      KatakataIrb::Types.type_from_object result
    end

    def get_cvar(nesting, path, name, _key = nil)
      return KatakataIrb::Types::NIL unless nesting

      result = path.reduce nesting do |mod, n|
        return KatakataIrb::Types::NIL unless mod.is_a?(Module) && module_own_constant?(mod, n)
        mod.const_get n
      end
      value = result.class_variable_get name if result.is_a?(Module) && name.size >= 3 && result.class_variable_defined?(name)
      Types.type_from_object value
    end

    def [](name)
      @cache[name] ||= (
        fallback = KatakataIrb::Types::NIL
        case BaseScope.type_by_name name
        when :ivar
          BaseScope.type_of(fallback: fallback) { OBJECT_INSTANCE_VARIABLE_GET_METHOD.bind_call(@self_object, name) }
        when :lvar
          BaseScope.type_of(fallback: fallback) { @binding.local_variable_get(name) }
        when :gvar
          BaseScope.type_of(fallback: fallback) { @binding.eval name if @global_variables.include? name }
        end
      )
    end

    def self_type
      KatakataIrb::Types.type_from_object @self_object
    end

    def local_variables() = @local_variables.to_a

    def global_variables() = @global_variables.to_a

    def self.type_of(fallback: KatakataIrb::Types::OBJECT)
      begin
        KatakataIrb::Types.type_from_object yield
      rescue
        fallback
      end
    end

    def self.type_by_name(name)
      if name.start_with? '@@'
        # "@@cvar" or "@@cvar::[module_id]::[module_path]"
        :cvar
      elsif name.start_with? '@'
        :ivar
      elsif name.start_with? '$'
        :gvar
      elsif name.start_with? '%'
        :internal
      elsif name[0].downcase != name[0] || name[0].match?(/\d/)
        # "ConstName" or "[module_id]::[const_path]"
        :const
      else
        :lvar
      end
    end
  end

  class Scope < BaseScope
    attr_reader :parent, :mergeable_changes, :level, :module_nesting

    def self.from_binding(binding, locals) = new(BaseScope.new(binding, binding.receiver, locals))

    def initialize(parent, table = {}, trace_ivar: true, trace_lvar: true, self_type: nil, nesting: nil)
      @parent = parent
      @level = parent.level + 1
      @trace_ivar = trace_ivar
      @trace_lvar = trace_lvar
      @module_nesting = nesting ? [nesting, *parent.module_nesting] : parent.module_nesting
      @self_type = self_type
      @terminated = false
      @jump_branches = []
      @mergeable_changes = @table = table.transform_values { [level, _1] }
    end

    def mutable? = true

    def terminated?
      @terminated
    end

    def terminate_with(type, value)
      return if terminated?
      store_jump type, value, @mergeable_changes
      terminate
    end

    def store_jump(type, value, changes)
      return if terminated?
      if has_own?(type)
        changes[type] = [level, value]
        @jump_branches << changes
      elsif @parent.mutable?
        @parent.store_jump(type, value, changes)
      end
    end

    def terminate
      return if terminated?
      @terminated = true
      @table = @mergeable_changes.dup
    end

    def trace?(name)
      return false unless @parent
      type = BaseScope.type_by_name(name)
      type == :ivar ? @trace_ivar : type == :lvar ? @trace_lvar : true
    end

    def level_of(name, var_type)
      case var_type
      when :ivar
        return level unless @trace_ivar
      when :gvar
        return 0
      end
      variable_level, = @table[name]
      variable_level || parent.level_of(name, var_type)
    end

    def get_const(nesting, path, key = nil)
      key ||= [nesting.__id__, path].join('::')
      _l, value = @table[key]
      value || @parent.get_const(nesting, path, key)
    end

    def get_cvar(nesting, path, name, key = nil)
      key ||= [name, nesting.__id__, path].join('::')
      _l, value = @table[key]
      value || @parent.get_cvar(nesting, path, name, key)
    end

    def [](name)
      type = BaseScope.type_by_name(name)
      if type == :const
        return get_const(nil, nil, name) || KatakataIrb::Types::NIL if name.include?('::')

        module_nesting.each do |(nesting, path)|
          value = get_const nesting, [*path, name]
          return value if value
        end
        return KatakataIrb::Types::NIL
      elsif type == :cvar
        return get_cvar(nil, nil, nil, name) if name.include?('::')

        nesting, path = module_nesting.first
        return get_cvar(nesting, path, name)
      end
      level, value = @table[name]
      if level
        value
      elsif trace? name
        @parent[name]
      elsif type == :ivar
        self_instance_variable_get name
      end
    end

    def set_const(nesting, path, value)
      key = [nesting.__id__, path].join('::')
      @table[key] = [0, value]
    end

    def set_cvar(nesting, path, name, value)
      key = [name, nesting.__id__, path].join('::')
      @table[key] = [0, value]
    end

    def []=(name, value)
      type = BaseScope.type_by_name(name)
      if type == :const
        if name.include?('::')
          @table[name] = [0, value]
        else
          parent_module, parent_path = module_nesting.first
          set_const parent_module, [*parent_path, name], value
        end
        return
      elsif type == :cvar
        if name.include?('::')
          @table[name] = [0, value]
        else
          parent_module, parent_path = module_nesting.first
          set_cvar parent_module, parent_path, name, value
        end
        return
      end
      variable_level = level_of name, type
      @table[name] = [variable_level, value] if variable_level
    end

    def self_type
      @self_type || @parent.self_type
    end

    def global_variables
      gvar_keys = @table.keys.select do |name|
        BaseScope.type_by_name(name) == :gvar
      end
      gvar_keys | @parent.global_variables
    end

    def local_variables
      lvar_keys = @table.keys.select do |name|
        BaseScope.type_by_name(name) == :lvar
      end
      lvar_keys |= @parent.local_variables if @trace_lvar
      lvar_keys
    end

    def table_constants
      constants = module_nesting.flat_map do |mod, path|
        prefix = [mod.__id__, *path].join('::') + '::'
        @table.keys.select { _1.start_with? prefix }.map { _1.delete_prefix(prefix).split('::').first }
      end.uniq
      constants |= @parent.table_constants if @parent.mutable?
      constants
    end

    def table_module_constants(mod)
      prefix = "#{mod.__id__}::"
      constants = @table.keys.select { _1.start_with? prefix }.map { _1.delete_prefix(prefix).split('::').first }
      constants |= @parent.table_constants if @parent.mutable?
      constants
    end

    def base_scope
      @parent.mutable? ? @parent.base_scope : @parent
    end

    def table_instance_variables
      ivars = @table.keys.select { BaseScope.type_by_name(_1) == :ivar }
      ivars |= @parent.table_instance_variables if @parent.mutable? && @trace_ivar
      ivars
    end

    def instance_variables
      self_singleton_types = self_type.types.grep(KatakataIrb::Types::SingletonType)
      singleton_classes = self_type.types.grep(KatakataIrb::Types::InstanceType).map(&:klass).select(&:singleton_class?)
      base_self = base_scope.self_object
      self_instance_variables = singleton_classes.flat_map do |singleton_class|
        if singleton_class.respond_to? :attached_object
          OBJECT_INSTANCE_VARIABLES_METHOD.bind_call(singleton_class.attached_object).map(&:to_s)
        elsif singleton_class == OBJECT_SINGLETON_CLASS_METHOD.bind_call(base_self)
          OBJECT_INSTANCE_VARIABLES_METHOD.bind_call(base_self).map(&:to_s)
        else
          []
        end
      end
      [
        self_singleton_types.flat_map { _1.module_or_class.instance_variables.map(&:to_s) },
        self_instance_variables || [],
        table_instance_variables
      ].inject(:|)
    end

    def self_instance_variable_get(name)
      self_objects = self_type.types.grep(KatakataIrb::Types::SingletonType).map(&:module_or_class)
      singleton_classes = self_type.types.grep(KatakataIrb::Types::InstanceType).map(&:klass).select(&:singleton_class?)
      base_self = base_scope.self_object
      singleton_classes.each do |singleton_class|
        if singleton_class.respond_to? :attached_object
          self_objects << singleton_class.attached_object
        elsif singleton_class == base_self.singleton_class
          self_objects << base_self
        end
      end
      types = self_objects.map do |object|
        BaseScope.type_of fallback: KatakataIrb::Types::NIL do
          OBJECT_INSTANCE_VARIABLE_GET_METHOD.bind_call(object, name)
        end
      end
      KatakataIrb::Types::UnionType[*types]
    end

    def table_class_variables
      cvars = @table.keys.filter_map { _1.split('::', 2).first if BaseScope.type_by_name(_1) == :cvar }
      cvars |= @parent.table_class_variables if @parent.mutable?
      cvars
    end

    def class_variables
      cvars = table_class_variables
      m, = module_nesting.first
      cvars |= m.class_variables.map(&:to_s) if m.is_a? Module
      cvars
    end

    def constants
      module_nesting.flat_map do |nest,|
        nest.constants
      end.map(&:to_s) | table_constants
    end

    def merge_jumps
      if terminated?
        @terminated = false
        @table = @mergeable_changes
        merge @jump_branches
        @terminated = true
      else
        merge [*@jump_branches, {}]
      end
    end

    def conditional(&block)
      run_branches(block, ->(_s) {}).first || KatakataIrb::Types::NIL
    end

    def never(&block)
      block.call Scope.new(self, { BREAK_RESULT => nil, NEXT_RESULT => nil, PATTERNMATCH_BREAK => nil, RETURN_RESULT => nil })
    end

    def run_branches(*blocks)
      results = []
      branches = []
      blocks.each do |block|
        scope = Scope.new self
        result = block.call scope
        next if scope.terminated?
        results << result
        branches << scope.mergeable_changes
      end
      terminate if branches.empty?
      merge branches
      results
    end

    def has_own?(name)
      @table.key? name
    end

    def update(child_scope)
      current_level = level
      child_scope.mergeable_changes.each do |name, (level, value)|
        self[name] = value if level <= current_level
      end
    end

    protected

    def merge(branches)
      current_level = level
      merge = {}
      branches.each do |changes|
        changes.each do |name, (level, value)|
          next if current_level < level
          (merge[name] ||= []) << value
        end
      end
      merge.each do |name, values|
        values << self[name] unless values.size == branches.size
        values.compact!
        self[name] = KatakataIrb::Types::UnionType[*values.compact] unless values.empty?
      end
    end
  end
end
