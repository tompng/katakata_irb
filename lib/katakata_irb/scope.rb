require 'set'
require_relative 'types'

module KatakataIrb
  class BaseScope
    SELF = '%self'
    BREAK_RESULT = '%break'
    NEXT_RESULT = '%next'
    RETURN_RESULT = '%return'
    PATTERNMATCH_BREAK = '%match'
    RAISE_BREAK = '%raise'

    def initialize(binding, self_object)
      @binding, @self_object = binding, self_object
      @cache = { SELF => KatakataIrb::Types.type_from_object(self_object) }
      @local_variables = binding.local_variables.map(&:to_s).to_set
    end

    def level() = 0

    def level_of(name)
      has?(name) ? 0 : nil
    end

    def mutable?() = false

    def [](name)
      @cache[name] ||= (
        fallback = KatakataIrb::Types::NIL
        case BaseScope.type_by_name name
        when :cvar
          KatakataIrb::TypeSimulator.type_of(fallback: fallback) { @self_object.class_variable_get name }
        when :ivar
          KatakataIrb::TypeSimulator.type_of(fallback: fallback) { @self_object.instance_variable_get name }
        when :lvar
          KatakataIrb::TypeSimulator.type_of(fallback: fallback) { @binding.local_variable_get(name) }
        when :const
          KatakataIrb::TypeSimulator.type_of(fallback: fallback) { @binding.eval name }
        end
      )
    end

    def self_type
      self[SELF]
    end

    def local_variables
      @local_variables.to_a
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
      elsif name[0].downcase != name[0]
        :const
      else
        :lvar
      end
    end

    def has?(name)
      case BaseScope.type_by_name name
      when :lvar
        @local_variables.include? name
      when :const
        @binding.eval("#{name};true") rescue false
      when :gvar, :cvar, :ivar
        true
      when :internal
        true
      end
    end
  end

  class Scope < BaseScope
    attr_reader :parent, :jump_branches, :mergeable_changes, :level

    def self.from_binding(binding) = new(BaseScope.new(binding, binding.eval('self')))

    def initialize(parent, table = {}, trace_cvar: true, trace_ivar: true, trace_lvar: true, passthrough: false)
      @table = table
      @parent = parent
      @level = parent.level + (passthrough ? 0 : 1)
      @trace_cvar = trace_cvar
      @trace_ivar = trace_ivar
      @trace_lvar = trace_lvar
      @passthrough = passthrough
      @terminated = false
      @jump_branches = []
      @mergeable_changes = @changes = table.transform_values { [level, _1] }
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
      @terminated = true
      @changes = {}
    end

    def branch_table_clone() = @tables.last.dup

    def trace?(name)
      return false unless @parent
      type = BaseScope.type_by_name(name)
      type == :cvar ? @trace_cvar : type == :ivar ? @trace_ivar : type == :lvar ? @trace_lvar : true
    end

    def level_of(name)
      has_own?(name) ? level : parent.level_of(name)
    end

    def [](name)
      level, value = @changes[name]
      if level
        value
      elsif trace? name
        @parent[name] if trace? name
      end
    end

    def []=(name, value)
      variable_level = level_of(name) || level
      @changes[name] = [variable_level, value]
    end

    def self_type
      self[SELF]
    end

    def local_variables
      lvar_keys = @changes.keys.select do |name|
        BaseScope.type_by_name(name) == :lvar
      end
      lvar_keys |= @parent.local_variables if @trace_lvar
      lvar_keys
    end

    def merge_jumps
      if terminated?
        merge @jump_branches
      else
        merge [*@jump_branches, {}]
      end
    end

    def conditional(&block)
      run_branches(block, ->(_s) {}).first || KatakataIrb::Types::NIL
    end

    def never(&block)
      block.call Scope.new(self, { BREAK_RESULT => nil, NEXT_RESULT => nil, PATTERNMATCH_BREAK => nil, RETURN_RESULT => nil, RAISE_BREAK => nil }, passthrough: true)
    end

    def run_branches(*blocks)
      results = []
      branches = []
      blocks.each do |block|
        scope = Scope.new self, passthrough: true
        result = block.call scope
        next if scope.terminated?
        results << result
        branches << scope.mergeable_changes
      end
      terminate if branches.empty?
      merge branches
      results
    end

    def has?(name)
      has_own?(name) || (trace?(name) && @parent.has?(name))
    end

    def has_own?(name)
      @changes.key? name
    end

    def update(child_scope)
      terminate if child_scope.terminated?
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
        self[name] = KatakataIrb::Types::UnionType[*values.compact]
      end
    end
  end
end
