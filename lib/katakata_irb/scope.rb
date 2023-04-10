require 'set'
require_relative 'types'

module KatakataIrb
  class BaseScope
    def initialize(binding, self_object)
      @binding, @self_object = binding, self_object
      @cache = { Scope::SELF => KatakataIrb::Types.type_from_object(self_object) }
      @local_variables = binding.local_variables.map(&:to_s).to_set
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
      self[Scope::SELF]
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

  class Scope
    SELF = '%self'
    BREAK_RESULT = '%break'
    NEXT_RESULT = '%next'
    RETURN_RESULT = '%return'
    PATTERNMATCH_BREAK = '%match'
    RAISE_BREAK = '%raise'

    attr_reader :parent, :jump_branches

    def self.from_binding(binding) = new(BaseScope.new(binding, binding.eval('self')))

    def initialize(parent, table = {}, trace_cvar: true, trace_ivar: true, trace_lvar: true, passthrough: false)
      @tables = [table]
      @parent = parent
      @trace_cvar = trace_cvar
      @trace_ivar = trace_ivar
      @trace_lvar = trace_lvar
      @passthrough = passthrough
      @terminated = false
      @jump_branches = []
    end

    def mutable? = true

    def terminated?
      @terminated
    end

    def terminate_with(type, value)
      return if terminated?
      self[type] = value
      store_jump type
      terminate
    end

    def store_jump(type)
      scopes = ancestors.select(&:mutable?)
      scope = scopes.find { _1.has_own? type } || scopes.last
      index = scopes.index scope
      scope.jump_branches << scopes.drop(index).map(&:branch_table_clone)
    end

    def terminate
      @terminated = true
    end

    def branch_table_clone() = @tables.last.dup

    def trace?(name)
      return false unless @parent
      type = BaseScope.type_by_name(name)
      type == :cvar ? @trace_cvar : type == :ivar ? @trace_ivar : type == :lvar ? @trace_lvar : true
    end

    def [](name)
      @tables.reverse_each do |table|
        return table[name] if table.key? name
      end
      @parent[name] if trace? name
    end

    def []=(name, type)
      return if terminated?
      if @passthrough && BaseScope.type_by_name(name) != :internal
        @parent[name] = type
      elsif trace?(name) && @parent.mutable? && !@tables.any? { _1.key? name } && @parent.has?(name)
        @parent[name] = type
      else
        @tables.last[name] = type
      end
    end

    def self_type
      self[SELF]
    end

    def local_variables
      lvar_keys = @tables.flat_map(&:keys).select do |name|
        BaseScope.type_by_name(name) == :lvar
      end
      lvar_keys |= @parent.local_variables if @trace_lvar
      lvar_keys
    end

    def start_branch
      @tables << {}
    end

    def end_branch
      @tables.pop
    end

    def merge_jumps
      if terminated?
        merge @jump_branches
      else
        merge [*@jump_branches, [{}] * ancestors.size]
      end
    end

    def merge_branch(tables)
      target_table = @tables.last
      keys = tables.flat_map(&:keys).uniq
      keys.each do |key|
        original_value = self[key]
        target_table[key] = KatakataIrb::Types::UnionType[*tables.map { _1[key] || original_value }.compact.uniq]
      end
    end

    def conditional(&block)
      run_branches(block, -> {}).first || KatakataIrb::Types::NIL
    end

    def never(&block)
      branch(&block)
    end

    def run_branches(*blocks)
      results = blocks.map { branch(&_1) }.reject(&:last)
      merge results.map { _2 }
      if results.empty?
        terminate
        []
      else
        results.map(&:first)
      end
    end

    def has?(name)
      has_own?(name) || (trace?(name) && @parent.has?(name))
    end

    def has_own?(name)
      @tables.any? { _1.key? name }
    end

    private

    def ancestors
      scopes = [self]
      scopes << scopes.last.parent while scopes.last.parent&.mutable?
      scopes
    end

    def before_branch
      @terminated = false
      scopes = ancestors
      scopes.each(&:start_branch)
      scopes
    end

    def after_branch(scopes)
      scopes.map(&:end_branch)
    end

    def branch
      scopes = before_branch
      result = yield
      [result, after_branch(scopes), @terminated]
    end

    def merge(branches)
      scopes = ancestors
      scopes.zip(*branches).each do |scope, *tables|
        scope.merge_branch(tables)
      end
    end
  end
end
