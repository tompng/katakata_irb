require 'set'
require_relative 'types'

module KatakataIrb
  class BaseScope
    BREAK_RESULT = '%break'
    NEXT_RESULT = '%next'
    RETURN_RESULT = '%return'
    PATTERNMATCH_BREAK = '%match'
    RAISE_BREAK = '%raise'

    attr_reader :module_nesting

    def initialize(binding, self_object, local_variables)
      @binding = binding
      @self_object = self_object
      @cache = {}
      @module_nesting = binding.eval 'Module.nesting'
      binding_local_variables = binding.local_variables
      uninitialized_locals = local_variables - binding_local_variables
      uninitialized_locals.each { @cache[_1] = KatakataIrb::Types::NIL }
      @local_variables = (local_variables | binding_local_variables).map(&:to_s).to_set
      @global_variables = Kernel.global_variables.map(&:to_s).to_set
    end

    def level() = 0

    def level_of(_name) = 0

    def mutable?() = false

    def get_const(absolute_name)
      BaseScope.type_of(fallback: nil) { @binding.eval absolute_name }
    end

    def [](name)
      @cache[name] ||= (
        fallback = KatakataIrb::Types::NIL
        case BaseScope.type_by_name name
        when :cvar
          BaseScope.type_of(fallback: fallback) { @self_object.class_variable_get name }
        when :ivar
          BaseScope.type_of(fallback: fallback) { @self_object.instance_variable_get name }
        when :lvar
          BaseScope.type_of(fallback: fallback) { @binding.local_variable_get(name) }
        when :const
          BaseScope.type_of(fallback: fallback) { @binding.eval name }
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
        :cvar
      elsif name.start_with? '@'
        :ivar
      elsif name.start_with? '$'
        :gvar
      elsif name.start_with? '%'
        :internal
      elsif name.start_with?('::') || name[0].downcase != name[0]
        :const
      else
        :lvar
      end
    end
  end

  class Scope < BaseScope
    attr_reader :parent, :mergeable_changes, :level, :module_nesting

    def self.from_binding(binding, locals) = new(BaseScope.new(binding, binding.eval('self'), locals))

    def initialize(parent, table = {}, trace_cvar: true, trace_ivar: true, trace_lvar: true, self_type: nil, nesting: nil)
      @parent = parent
      @level = parent.level + 1
      @trace_cvar = trace_cvar
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
      type == :cvar ? @trace_cvar : type == :ivar ? @trace_ivar : type == :lvar ? @trace_lvar : true
    end

    def level_of(name)
      variable_level, = @table[name]
      variable_level || parent.level_of(name)
    end

    def get_const(absolute_name)
      l, value = @table[absolute_name]
      l ? value : @parent.get_const(absolute_name)
    end

    def [](name)
      if BaseScope.type_by_name(name) == :const
        return get_const name if name.start_with? '::'

        module_nesting.each do |nesting|
          n = "#{nesting}::#{name}"
          n = "::#{n}" unless n.start_with? '::'
          v = get_const(n)
          return v if v
        end
        return get_const("::#{name}") || KatakataIrb::Types::NIL
      end
      level, value = @table[name]
      if level
        value
      elsif trace? name
        @parent[name] if trace? name
      end
    end

    def []=(name, value)
      if BaseScope.type_by_name(name) == :const
        if name.start_with? '::'
          @table[name] = [0, value]
        else
          absolute_name = "#{module_nesting.first}::#{name}"
          absolute_name = "::#{absolute_name}" unless absolute_name.start_with? '::'
          @table[absolute_name] = [0, value]
        end
        return
      end
      variable_level = level_of name
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
      constants = [*module_nesting, ''].flat_map do |nest|
        prefix = nest.is_a?(Module) ? "::#{nest}::" : "#{nest}::"
        prefix = "::#{prefix}" unless prefix.start_with? '::'
        @table.keys.select { _1.start_with? prefix }.map { _1.delete_prefix prefix }
      end.uniq
      constants |= @parent.table_constants if @parent.mutable?
      constants
    end

    def table_instance_variables
      ivars = @table.keys.select { BaseScope.type_by_name(_1) == :ivar }
      ivars |= @parent.table_instance_variables if @parent.mutable? && @trace_ivar
      ivars
    end

    def instance_variables
      self_singleton_types = self_type.types.grep(KatakataIrb::Types::SingletonType)
      self_singleton_types.flat_map { _1.module_or_class.instance_variables } | table_instance_variables
    end

    def class_variables
      cvars = @table.keys.select { BaseScope.type_by_name(_1) == :cvar }
      cvars |= @parent.class_variables if @parent.mutable? && @trace_cvar
      unless @trace_cvar
        m = module_nesting.first
        cvars |= m.class_variables if m.is_a? Module
      end
      cvars
    end

    def constants
      [*module_nesting, Object].flat_map do |nest|
        nest.is_a?(Module) ? nest.constants : (eval(nest).constants rescue [])
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
      block.call Scope.new(self, { BREAK_RESULT => nil, NEXT_RESULT => nil, PATTERNMATCH_BREAK => nil, RETURN_RESULT => nil, RAISE_BREAK => nil })
    end

    def run(*args, **option)
      scope = Scope.new(self, *args, **option)
      yield scope
      merge_jumps
      update scope
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
