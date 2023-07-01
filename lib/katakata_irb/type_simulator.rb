require 'ripper'
require 'set'
require_relative 'types'
require_relative 'scope'

class KatakataIrb::TypeSimulator
  class DigTarget
    def initialize(parents, receiver, &block)
      @dig_ids = parents.to_h { [_1.node_id, true] }
      @target_id = receiver.node_id
      @block = block
    end

    def dig?(node) = @dig_ids[node.node_id]
    def target?(node) = @target_id == node.node_id
    def resolve(type, scope)
      @block.call type, scope
    end
  end

  module ASTNodeMatcher
    refine RubyVM::AbstractSyntaxTree::Node do
      def deconstruct_keys(_keys)
        { type: type, children: children }
      end
    end
  end
  using ASTNodeMatcher

  OBJECT_METHODS = {
    to_s: KatakataIrb::Types::STRING,
    to_str: KatakataIrb::Types::STRING,
    to_a: KatakataIrb::Types::ARRAY,
    to_ary: KatakataIrb::Types::ARRAY,
    to_h: KatakataIrb::Types::HASH,
    to_hash: KatakataIrb::Types::HASH,
    to_i: KatakataIrb::Types::INTEGER,
    to_int: KatakataIrb::Types::INTEGER,
    to_f: KatakataIrb::Types::FLOAT,
    to_c: KatakataIrb::Types::COMPLEX,
    to_r: KatakataIrb::Types::RATIONAL
  }

  def initialize(dig_targets)
    @dig_targets = dig_targets
  end

  def simulate_evaluate(node, scope, context)
    result = simulate_evaluate_inner(node, scope, context)
    if @dig_targets.target?(node)
      @dig_targets.resolve result, scope
    end
    result
  end

  # Context: case_target, errinfo, nil_dvar. TODO: module_nesting(for const ref), method_name(for super type)
  def simulate_evaluate_inner(node, scope, context)
    type = node.type
    children = node.children
    case type
    in :BLOCK
      children.map { simulate_evaluate _1, scope, context }.last
    in :BEGIN
      statement = children.first
      if statement
        simulate_evaluate_inner statement, scope, context
      else
        KatakataIrb::Types::NIL
      end
    in :SCOPE
      table, args, statement = children
      table = table.compact
      new_scope = KatakataIrb::Scope.new(scope, table.to_h { [_1, nil] })
      simulate_evaluate args.children[1], new_scope, context if args
      result = simulate_evaluate statement, new_scope, context
      scope.update new_scope
      result
    in :ERRINFO
      context[:errinfo] || KatakataIrb::Types::NIL
    in [:def | :defs,]
      # sexp in [:def, _method_name_exp, params, body_stmt]
      # sexp in [:defs, receiver_exp, _dot_exp, _method_name_exp, params, body_stmt]
      # if receiver_exp
      #   receiver_exp in [:paren, receiver_exp]
      #   self_type = simulate_evaluate receiver_exp, scope, context
      # else
      #   current_self_types = scope.self_type.types
      #   self_types = current_self_types.map do |type|
      #     if type.is_a?(KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
      #       KatakataIrb::Types::InstanceType.new type.module_or_class
      #     else
      #       type
      #     end
      #   end
      #   self_type = KatakataIrb::Types::UnionType[*self_types]
      # end
      # if @dig_targets.dig? sexp
      #   params in [:paren, params]
      #   params ||= [:params, nil, nil, nil, nil, nil, nil, nil] # params might be nil in ruby 3.0
      #   params_table = extract_param_names(params).to_h { [_1, KatakataIrb::Types::NIL] }
      #   method_scope = KatakataIrb::Scope.new(
      #     scope,
      #     { **params_table, KatakataIrb::Scope::SELF => self_type, KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil },
      #     trace_lvar: false
      #   )
      #   evaluate_assign_params params, [], method_scope
      #   method_scope.conditional { evaluate_param_defaults params, _1 }
      #   simulate_evaluate body_stmt, method_scope, context
      #   method_scope.merge_jumps
      #   scope.update method_scope
      # end
      # KatakataIrb::Types::SYMBOL
    in :NIL
      KatakataIrb::Types::NIL
    in :TRUE
      KatakataIrb::Types::TRUE
    in :FALSE
      KatakataIrb::Types::FALSE
    in :LIT
      KatakataIrb::Types::InstanceType.new children.first.class
    in :STR | :XSTR
      KatakataIrb::Types::STRING
    in :DREGX | :DSTR | :DXSTR | :DSYM
      _s, statement, list = children
      [statement, *list&.children].each {
        simulate_evaluate _1.children.first, scope, context if _1.type == :EVSTR
      }
      case type
      when :DREGX
        KatakataIrb::Types::REGEXP
      when :DSYM
        KatakataIrb::Types::SYMBOL
      else
        KatakataIrb::Types::STRING
      end
    in :BACK_REF
      KatakataIrb::Types::UnionType[KatakataIrb::Types::STRING, KatakataIrb::Types::NIL]
    in :ZLIST
      KatakataIrb::Types::ARRAY
    in :LIST
      types = children.compact.map do
        simulate_evaluate _1, scope, context
      end
      KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*types]
    in :HASH
      hash_entries_to_type evaluate_hash_entries(node, scope, context)
    in :ARGSPUSH | :ARGSCAT
      args = evaluate_args(node, scope, context)
      types = args.flat_map do |elem|
        case elem
        when KatakataIrb::Types::Splat
          array_elem, non_array = partition_to_array elem.item.nonnillable, :to_a
          [*array_elem, *non_array]
        when Array
          hash_entries_to_type(elem)
        else
          elem
        end
      end
      elem_type = KatakataIrb::Types::UnionType[*types]
      KatakataIrb::Types::InstanceType.new(Array, Elem: elem_type)
    in :CONST
      scope[children.first.to_s]
    in :COLON2
      receiver_node, name = children
      if receiver_node
        receiver = simulate_evaluate receiver_node, scope, context
        receiver.is_a?(KatakataIrb::Types::SingletonType) ? KatakataIrb::BaseScope.type_of { receiver.module_or_class.const_get name } : KatakataIrb::Types::NIL
      else
        scope[name.to_s] || KatakataIrb::Types::NIL
      end
    in :COLON3
      KatakataIrb::BaseScope.type_of { Object.const_get children.first }
    in :SELF
      scope.self_type
    in :VCALL
      simulate_call scope.self_type, children.first, [], nil, nil
    in :FCALL
      name, list = children
      evaluate_call scope.self_type, name, list, scope: scope, context: context
    in :CALL | :QCALL
      receiver, name, list = children
      receiver_type = simulate_evaluate receiver, scope, context
      optional_chain = type == :QCALL
      evaluate_call receiver_type, name, list, scope: scope, optional_chain: type == :QCALL, context: context
    in :ITER
      call, block = children
      receiver, method, list, optional_chain = (
        case call.type
        in :FCALL
          [scope.self_type, call.children[0], call.children[1], false]
        in :CALL | :QCALL
          [simulate_evaluate(call.children[0], scope, context), call.children[1], call.children[2], type == :QCALL]
        end
      )
      evaluate_call receiver, method, list, scope: scope, block: block, optional_chain: optional_chain, context: context
    in :OPCALL
      a, op, b = node.children
      atype = simulate_evaluate a, scope, context
      args = b ? [simulate_evaluate(b.children.first, scope, context)] : []
      simulate_call atype, op, args, nil, nil
    in [:lambda, params, statements]
      # params in [:paren, params] # ->{}, -> do end
      # statements in [:bodystmt, statements, _unknown, _unknown, _unknown] # -> do end
      # params in [:paren, params]
      # params_table = extract_param_names(params).to_h { [_1, KatakataIrb::Types::NIL] }
      # block_scope = KatakataIrb::Scope.new scope, { **params_table, KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }
      # block_scope.conditional do |s|
      #   evaluate_assign_params params, [], s
      #   s.conditional { evaluate_param_defaults params, _1 }
      #   statements.each { simulate_evaluate _1, s, context }
      # end
      # block_scope.merge_jumps
      # scope.update block_scope
      # KatakataIrb::Types::ProcType.new
    in :DVAR
      children => [name]
      (name ? scope[name] : context[:nil_dvar]) || KatakataIrb::Types::NIL
    in :LVAR | :GVAR | :IVAR | :CVAR
      scope[children.first] || KatakataIrb::Types::NIL
    in :LASGN | :GASGN | :IASGN | :CVASGN | :DASGN
      children => [name, value]
      scope[name] = simulate_evaluate(value, scope, context)
    in :ATTRASGN
      children => [receiver, assign_method, value]
      simulate_evaluate receiver, scope, context
      simulate_evaluate value, scope, context
    in :MASGN
      children => [value_node, pre, post]
      value = simulate_evaluate value_node, scope, context
      evaluate_massign node, value, scope: scope, context: context
    in :IF | :UNLESS
      cond, val1, val2 = children
      simulate_evaluate cond, scope, context
      KatakataIrb::Types::UnionType[*scope.run_branches(
        -> { val1 ? simulate_evaluate(val1, _1, context) : KatakataIrb::Types::NIL },
        -> { val2 ? simulate_evaluate(val2, _1, context) : KatakataIrb::Types::NIL },
      )]
    in :WHILE | :UNTIL
      children => [cond, statement, true]
      inner_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::BREAK_RESULT => nil }, passthrough: true
      inner_scope.conditional { simulate_evaluate statement, _1, context }
      inner_scope.merge_jumps
      scope.update inner_scope
      breaks = inner_scope[KatakataIrb::Scope::BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, KatakataIrb::Types::NIL] : KatakataIrb::Types::NIL
    in :BREAK | :NEXT | :RETURN
      value = children.first
      internal_key = type == :BREAK ? KatakataIrb::Scope::BREAK_RESULT : type == :NEXT ? KatakataIrb::Scope::NEXT_RESULT : KatakataIrb::Scope::RETURN_RESULT
      if value&.type == :LIST
        values = value.children.compact.map { simulate_evaluate _1, scope, context }
        jump_value = values.size == 1 ? values.first : KatakataIrb::Types::InstanceType.new(Array, Elem: KatakataIrb::Types::UnionType[*values])
      else
        jump_value = KatakataIrb::Types::NIL
      end
      scope.terminate_with internal_key, jump_value
      KatakataIrb::Types::NIL
    in :YIELD
      simulate_evaluate children.first, scope, context
      KatakataIrb::Types::OBJECT
    in :REDO | :RETRY
      scope.terminate
    in :ZSUPER
      KatakataIrb::Types::OBJECT
    in [:super, args]
      # args, kwargs, _block = retrieve_method_args args
      # args.each do |arg|
      #   item = arg.is_a?(KatakataIrb::Types::Splat) ? arg.item : arg
      #   simulate_evaluate item, scope, context
      # end
      # kwargs_type kwargs, scope
      # KatakataIrb::Types::OBJECT
    in :ENSURE
      statement, ensure_statement = children
      return_type = simulate_evaluate statement, scope, context
      simulate_evaluate ensure_statement, scope, context
      return_type
    in :RESCUE
      statement, rescue_statement = children
      rescue_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::RAISE_BREAK => nil }, passthrough: true
      return_type = simulate_evaluate statement, rescue_scope, context
      rescue_scope.merge_jumps
      scope.update rescue_scope
      KatakataIrb::Types::UnionType[return_type, scope.conditional { simulate_evaluate rescue_statement, _1, context }]
    in :RESBODY
      error_classlist_node, statement, else_statement = children
      if error_classlist_node
        classlist_type = simulate_evaluate error_classlist_node, scope, context
        types = classlist_type.params['Elem']&.types if classlist_type.is_a?(KatakataIrb::Types::InstanceType) && classlist_type.klass == Array
      end
      error_types = (types || []).filter_map do |type|
        KatakataIrb::Types::InstanceType.new type.module_or_class if type.is_a? KatakataIrb::Types::SingletonType
      end
      error_types << KatakataIrb::Types::InstanceType.new(StandardError) if error_types.empty?
      error_type = KatakataIrb::Types::UnionType[*error_types]
      if else_statement
        scope.run_branches(
          ->{ simulate_evaluate statement, _1, { **context, errinfo: error_type } },
          ->{ simulate_evaluate else_statement, _1, context }
        )
      else
        simulate_evaluate statement, scope, { **context, errinfo: error_type }
      end
      KatakataIrb::Types::NIL
    in :MODULE
      children => [module_stmt, body_stmt]
      module_types = simulate_evaluate(module_stmt, scope, context).types.grep(KatakataIrb::Types::SingletonType)
      module_types << KatakataIrb::Types::MODULE if module_types.empty?
      module_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::SELF => KatakataIrb::Types::UnionType[*module_types], KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
      result = simulate_evaluate body_stmt, module_scope, context
      scope.update module_scope
      result
    in :SCLASS
      children => [klass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope, context).types.filter_map do |type|
        KatakataIrb::Types::SingletonType.new type.klass if type.is_a? KatakataIrb::Types::InstanceType
      end
      klass_types = [KatakataIrb::Types::CLASS] if klass_types.empty?
      sclass_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::SELF => KatakataIrb::Types::UnionType[*klass_types], KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
      result = simulate_evaluate body_stmt, sclass_scope, context
      scope.update sclass_scope
      result
    in :CLASS
      children => [klass_stmt, superclass_stmt, body_stmt]
      klass_types = simulate_evaluate(klass_stmt, scope, context).types
      klass_types += simulate_evaluate(superclass_stmt, scope, context).types if superclass_stmt
      klass_types = klass_types.select do |type|
        type.is_a?(KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
      end
      klass_types << KatakataIrb::Types::CLASS if klass_types.empty?
      klass_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::SELF => KatakataIrb::Types::UnionType[*klass_types], KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil, KatakataIrb::Scope::RETURN_RESULT => nil }, trace_cvar: false, trace_ivar: false, trace_lvar: false)
      result = simulate_evaluate body_stmt, klass_scope, context
      scope.update klass_scope
      result
    in :FOR
      list_node, statement = children
      list_type = simulate_evaluate list_node, scope, context
      elem_type = simulate_call list_type, :first, [], nil, nil
      inner_scope = KatakataIrb::Scope.new scope, { KatakataIrb::Scope::BREAK_RESULT => nil }, passthrough: true
      scope.conditional do |s|
        simulate_evaluate statement, s, { **context, nil_dvar: elem_type }
      end
      inner_scope.merge_jumps
      scope.update inner_scope
      breaks = inner_scope[KatakataIrb::Scope::BREAK_RESULT]
      breaks ? KatakataIrb::Types::UnionType[breaks, list_type] : list_type
    in [:when, pattern, if_statements, else_statement]
      # eval_pattern = lambda do |s, pattern, *rest|
      #   simulate_evaluate pattern, s, context
      #   scope.conditional { eval_pattern.call(_1, *rest) } if rest.any?
      # end
      # if_branch = lambda do |s|
      #   eval_pattern.call(s, *pattern)
      #   if_statements.map { simulate_evaluate _1, s, context }.last
      # end
      # else_branch = lambda do |s|
      #   pattern.each { simulate_evaluate _1, s, context }
      #   simulate_evaluate(else_statement, s, { **context, case_target: case_target })
      # end
      # if if_statements && else_statement
      #   KatakataIrb::Types::UnionType[*scope.run_branches(if_branch, else_branch)]
      # else
      #   KatakataIrb::Types::UnionType[scope.conditional { (if_branch || else_branch).call _1 }, KatakataIrb::Types::NIL]
      # end
    in [:in, [:var_field, [:@ident, name,]], if_statements, else_statement]
      # scope.never { simulate_evaluate else_statement, scope, context } if else_statement
      # scope[name] = context[:case_target] || KatakataIrb::Types::OBJECT
      # if_statements ? if_statements.map { simulate_evaluate _1, scope, context }.last : KatakataIrb::Types::NIL
    in [:in, pattern, if_statements, else_statement]
      # pattern_scope = KatakataIrb::Scope.new(scope, { KatakataIrb::Scope::PATTERNMATCH_BREAK => nil }, passthrough: true)
      # results = pattern_scope.run_branches(
      #   ->(s) {
      #     match_pattern context[:case_target], pattern, s
      #     if_statements ? if_statements.map { simulate_evaluate _1, s, context }.last : KatakataIrb::Types::NIL
      #   },
      #   ->(s) {
      #     else_statement ? simulate_evaluate(else_statement, s, { **context, case_target: case_target }) : KatakataIrb::Types::NIL
      #   }
      # )
      # pattern_scope.merge_jumps
      # scope.update pattern_scope
      # KatakataIrb::Types::UnionType[*results]
    in :CASE
      children => [target_node, match_node]
      target = target_exp ? simulate_evaluate(target_node, scope, context) : KatakataIrb::Types::NIL
      simulate_evaluate match_node, scope, { **context, case_target: target }
    in :DOT2 | :DOT3
      range_beg, range_end = children
      beg_type = simulate_evaluate range_beg, scope, context
      end_type = simulate_evaluate range_end, scope, context
      elem = (KatakataIrb::Types::UnionType[*[beg_type, end_type].compact]).nonnillable
      KatakataIrb::Types::InstanceType.new Range, { Elem: elem }
    in :DEFINED
      scope.conditional { simulate_evaluate children.first, _1, context }
      KatakataIrb::Types::UnionType[KatakataIrb::Types::STRING, KatakataIrb::Types::NIL]
    else
      $node = node
      KatakataIrb.log_puts :NOMATCH
      KatakataIrb.log_puts node.inspect
      KatakataIrb.log_puts node.children.inspect
      KatakataIrb.log_puts
      KatakataIrb::Types::NIL
    end
  end

  def evaluate_hash_entries(node, scope, context)
    node.children.first.children.each_slice(2).filter_map do |k, v|
      next unless v
      next [nil, simulate_evaluate(v, scope, context)] unless k

      key = k.type == :LIT && k.children.first.is_a?(Symbol) ? k.children.first : simulate_evaluate(k, scope, context)
      value = simulate_evaluate v, scope, context
      [key, value]
    end
  end

  def hash_entries_to_type(entries)
    keys = []
    values = []
    entries.each do |k, v|
      next unless k # TODO: splat
      keys << (k.is_a?(Symbol) ? KatakataIrb::Types::SYMBOL : k)
      values << v
    end
    key_type = KatakataIrb::Types::UnionType[*keys]
    value_type = KatakataIrb::Types::UnionType[*values]
    KatakataIrb::Types::InstanceType.new Hash, K: key_type, V: value_type
  end

  def evaluate_args_block(node, scope, context)
    if node.nil?
      [[], nil]
    elsif node.type == :BLOCK_PASS
      arg_node, block_node = node.children
      args = evaluate_args arg_node, scope, context
      block = block_node.type == :LIT ? block_node.children.first : simulate_evaluate(block_node, scope, context)
      [args, block]
    else
      [evaluate_args(node, scope, context), nil]
    end
  end

  def evaluate_args(node, scope, context)
    case node.type
    when :LIST
      args = node.children.compact.map do |value|
        value.type == :HASH ? evaluate_hash_entries(value, scope, context) : simulate_evaluate(value, scope, context)
      end
      args
    when :ARGSPUSH
      args_node, arg_node = node.children
      args = evaluate_args args_node, scope, context
      arg = arg_node.type == :HASH ? evaluate_hash_entries(arg_node, scope, context) : simulate_evaluate(arg_node, scope, context)
      [*args, arg]
    when :ARGSCAT
      args_node, splat = node.children
      args = evaluate_args args_node, scope, context
      [*args, KatakataIrb::Types::Splat.new(simulate_evaluate(splat, scope, context))]
    end
  end

  def match_pattern(target, pattern, scope)
    breakable = -> { scope.terminate_with KatakataIrb::Scope::PATTERNMATCH_BREAK, KatakataIrb::Types::NIL }
    types = target.types
    case pattern
    in [:var_field, [:@ident, name,]]
      scope[name] = target
    in [:var_ref,] # in Array, in ^a, in nil
    in [:@int | :@float | :@rational | :@imaginary | :@CHAR | :symbol_literal | :string_literal | :regexp_literal,]
    in [:begin, statement] # in (statement)
      simulate_evaluate statement, scope, context
      breakable.call
    in [:binary, lpattern, :|, rpattern]
      match_pattern target, lpattern, scope
      scope.conditional { match_pattern target, rpattern, _1 }
      breakable.call
    in [:binary, lpattern, :'=>', [:var_field, [:@ident, name,]] => rpattern]
      if lpattern in [:var_ref, [:@const, _const_name,]]
        const_value = simulate_evaluate lpattern, scope, context
        if const_value.is_a?(KatakataIrb::Types::SingletonType) && const_value.module_or_class.is_a?(Class)
          scope[name] = KatakataIrb::Types::InstanceType.new const_value.module_or_class
        else
          scope[name] = KatakataIrb::Types::OBJECT
        end
        breakable.call
      else
        match_pattern target, lpattern, scope
        match_pattern target, rpattern, scope
      end
    in [:aryptn, _unknown, items, splat, post_items]
      # TODO: deconstruct keys
      array_types = types.select { _1.is_a?(KatakataIrb::Types::InstanceType) && _1.klass == Array }
      elem = KatakataIrb::Types::UnionType[*array_types.filter_map { _1.params[:Elem] }]
      items&.each do |item|
        match_pattern elem, item, scope
      end
      if splat in [:var_field, [:@ident, name,]]
        scope[name] = KatakataIrb::Types::InstanceType.new Array, Elem: elem
        breakable.call
      end
      post_items&.each do |item|
        match_pattern elem, item, scope
      end
    in [:hshptn, _unknown, items, splat]
      # TODO: deconstruct keys
      hash_types = types.select { _1.is_a?(KatakataIrb::Types::InstanceType) && _1.klass == Hash }
      key_type = KatakataIrb::Types::UnionType[*hash_types.filter_map { _1.params[:K] }]
      value_type = KatakataIrb::Types::UnionType[*hash_types.filter_map { _1.params[:V] }]
      items&.each do |key_pattern, value_pattern|
        if (key_pattern in [:@label, label,]) && !value_pattern
          name = label.delete ':'
          scope[name] = value_type
          breakable.call
        end
        match_pattern value_type, value_pattern, scope if value_pattern
      end
      if splat in [:var_field, [:@ident, name,]]
        scope[name] = KatakataIrb::Types::InstanceType.new Hash, K: key_type, V: value_type
        breakable.call
      end
    in [:if_mod, cond, ifpattern]
      match_pattern target, ifpattern, scope
      simulate_evaluate cond, scope, context
      breakable.call
    in [:dyna_symbol,]
    in [:const_path_ref,]
    else
      KatakataIrb.log_puts "Unimplemented match pattern: #{pattern}"
    end
  end

  def sized_splat(value, method, size)
    array_elem, non_array = partition_to_array value, method
    values = [KatakataIrb::Types::UnionType[*array_elem, *non_array]]
    values += [array_elem] * (size - 1) if array_elem && size >= 1
    values
  end

  def to_array_item(value, method)
    array_elem, non_array = partition_to_array value, method
    KatakataIrb::Types::UnionType[*array_elem, *non_array]
  end

  def partition_to_array(value, method)
    arrays, non_arrays = value.types.partition { _1.is_a?(KatakataIrb::Types::InstanceType) && _1.klass == Array }
    non_arrays.select! do |type|
      to_array_result = simulate_call type, method, [], nil, nil, name_match: false
      if to_array_result.is_a?(KatakataIrb::Types::InstanceType) && to_array_result.klass == Array
        arrays << to_array_result
        false
      else
        true
      end
    end
    array_elem = arrays.empty? ? nil : KatakataIrb::Types::UnionType[*arrays.map { _1.params[:Elem] || KatakataIrb::Types::OBJECT }]
    non_array = non_arrays.empty? ? nil : KatakataIrb::Types::UnionType[*non_arrays]
    [array_elem, non_array]
  end

  def evaluate_massign(target, value, scope:, context:)
    case target.type
    in :ATTRASGN
      target.children => [receiver, _method, list]
      simulate_evaluate receiver, scope, context
      if list
        list.children.compact.each { simulate_evaluate _1, scope, context }
      end
    in :POSTARG
      target.children => [splat, rest]
      array = KatakataIrb::Types::InstanceType.new Array, Elem: value
      evaluate_massign splat, array, scope: scope, context: context
      evaluate_massign rest, value, scope: scope, context: context
    in :LASGN | :GASGN | :IASGN | :CVASGN | :DASGN
      target.children => [name, nil]
      scope[name] = value
    in :LIST
      target.children.compact.each do
        evaluate_massign _1, value, scope: scope, context: context
      end
    in :MASGN
      elem = to_array_item value, :to_ary
      target.children => [_value, pre, post]
      evaluate_massign pre, elem, scope: scope, context: context if pre
      evaluate_massign post, elem, scope: scope, context: context if post
    end
  end

  def kwargs_type(kwargs, scope)
    return if kwargs.empty?
    keys = []
    values = []
    kwargs.each do |kv|
      if kv.is_a? KatakataIrb::Types::Splat
        hash = simulate_evaluate kv.item, scope, context
        unless hash.is_a?(KatakataIrb::Types::InstanceType) && hash.klass == Hash
          hash = simulate_call hash, :to_hash, [], nil, nil
        end
        if hash.is_a?(KatakataIrb::Types::InstanceType) && hash.klass == Hash
          keys << hash.params[:K] if hash.params[:K]
          values << hash.params[:V] if hash.params[:V]
        end
      else
        key, value = kv
        keys << ((key in [:@label,]) ? KatakataIrb::Types::SYMBOL : simulate_evaluate(key, scope, context))
        values << simulate_evaluate(value, scope, context)
      end
    end
    KatakataIrb::Types::InstanceType.new(Hash, K: KatakataIrb::Types::UnionType[*keys], V: KatakataIrb::Types::UnionType[*values])
  end

  def retrieve_method_call(sexp)
    optional = -> { _1 in [:@op, '&.',] }
    case sexp
    in [:fcall | :vcall, [:@ident | :@const | :@kw | :@op, method,]] # hoge
      [nil, method, [], [], nil, false]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, :call]
      [receiver, :call, [], [], nil, optional[dot]]
    in [:call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, method]
      method => [:@ident | :@const | :@kw | :@op, method,] unless method == :call
      [receiver, method, [], [], nil, optional[dot]]
    in [:command, [:@ident | :@const | :@kw | :@op, method,], args] # hoge 1, 2
      args, kwargs, block = retrieve_method_args args
      [nil, method, args, kwargs, block, false]
    in [:command_call, receiver, [:@period,] | [:@op, '&.',] | :'::' => dot, [:@ident | :@const | :@kw | :@op, method,], args] # a.hoge 1; a.hoge 1, 2;
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block, optional[dot]]
    in [:method_add_arg, call, args]
      receiver, method, _arg, _kwarg, _block, opt = retrieve_method_call call
      args, kwargs, block = retrieve_method_args args
      [receiver, method, args, kwargs, block, opt]
    in [:method_add_block, call, block]
      receiver, method, args, kwargs, opt = retrieve_method_call call
      [receiver, method, args, kwargs, block, opt]
    end
  end

  def retrieve_method_args(sexp)
    case sexp
    in [:mrhs_add_star, args, star]
      args, = retrieve_method_args args
      [[*args, KatakataIrb::Types::Splat.new(star)], [], nil]
    in [:mrhs_new_from_args, [:args_add_star,] => args]
      args, = retrieve_method_args args
      [args, [], nil]
    in [:mrhs_new_from_args, [:args_add_star,] => args, last_arg]
      args, = retrieve_method_args args
      [[*args, last_arg], [], nil]
    in [:mrhs_new_from_args, args, last_arg]
      [[*args, last_arg], [], nil]
    in [:mrhs_new_from_args, args]
      [args, [], nil]
    in [:args_add_block, [:args_add_star,] => args, block_arg]
      args, kwargs, = retrieve_method_args args
      block_arg = [:void_stmt] if block_arg.nil? # method(*splat, &)
      [args, kwargs, block_arg]
    in [:args_add_block, [*args, [:bare_assoc_hash,] => kw], block_arg]
      block_arg = [:void_stmt] if block_arg.nil? # method(**splat, &)
      _, kwargs = retrieve_method_args kw
      [args, kwargs, block_arg]
    in [:args_add_block, [*args], block_arg]
      block_arg = [:void_stmt] if block_arg.nil? # method(arg, &)
      [args, [], block_arg]
    in [:bare_assoc_hash, kws]
      kwargs = []
      kws.each do |kw|
        if kw in [:assoc_splat, value,]
          kwargs << KatakataIrb::Types::Splat.new(value) if value
        elsif kw in [:assoc_new, [:@label, label,] => key, nil]
          name = label.delete ':'
          kwargs << [key, [:__var_ref_or_call, [name =~ /\A[A-Z]/ ? :@const : :@ident, name, [0, 0]]]]
        elsif kw in [:assoc_new, key, value]
          kwargs << [key, value]
        end
      end
      [[], kwargs, nil]
    in [:args_add_star, *args, [:bare_assoc_hash,] => kwargs]
      args, = retrieve_method_args [:args_add_star, *args]
      _, kwargs = retrieve_method_args kwargs
      [args, kwargs, nil]
    in [:args_add_star, pre_args, star_arg, *post_args]
      pre_args, = retrieve_method_args pre_args if pre_args in [:args_add_star,]
      args = star_arg ? [*pre_args, KatakataIrb::Types::Splat.new(star_arg), *post_args] : pre_args + post_args
      [args, [], nil]
    in [:arg_paren, args]
      args ? retrieve_method_args(args) : [[], [], nil]
    in [[:command | :command_call, ] => command_arg] # method(a b, c), method(a.b c, d)
      [[command_arg], [], nil]
    else
      [[], [], nil]
    end
  end

  def evaluate_call(receiver, method_name, list, scope:, block: nil, optional_chain: false, context: {})
    evaluate_method = lambda do |receiver, scope|
      list_args, block_arg = evaluate_args_block(list, scope, context)
      block ||= block_arg
      args = list_args.map do |elem|
        elem.is_a?(Array) ? hash_entries_to_type(elem) : elem
      end
      if list_args.last.is_a?(Array)
        args.pop
        kwargs = list_args.last.select { _1.is_a? Symbol }
      end

      if block
        if block.is_a?(Symbol)
          call_block_proc = ->(block_args, _self_type) do
            block_receiver, *rest = block_args
            block_receiver ? simulate_call(block_receiver || KatakataIrb::Types::OBJECT, block, rest, nil, nil) : KatakataIrb::Types::OBJECT
          end
        elsif block&.type == :SCOPE
          call_block_proc = ->(block_args, block_self_type) do
            table, args, body = block.children
            scope.conditional do |s|
              if params
                names = extract_param_names(params)
              else
                names = (1..max_numbered_params(body)).map { "_#{_1}" }
                params = [:params, names.map { [:@ident, _1, [0, 0]] }, nil, nil, nil, nil, nil, nil]
              end
              params_table = names.zip(block_args).to_h { [_1, _2 || KatakataIrb::Types::NIL] }
              table = { **params_table, KatakataIrb::Scope::BREAK_RESULT => nil, KatakataIrb::Scope::NEXT_RESULT => nil }
              table[KatakataIrb::Scope::SELF] = block_self_type if block_self_type
              block_scope = KatakataIrb::Scope.new s, table
              evaluate_assign_params params, block_args, block_scope
              block_scope.conditional { evaluate_param_defaults params, _1 } if params
              if type == :do_block
                result = simulate_evaluate body, block_scope, context
              else
                result = body.map { simulate_evaluate _1, block_scope, context }.last
              end
              block_scope.merge_jumps
              s.update block_scope
              nexts = block_scope[KatakataIrb::Scope::NEXT_RESULT]
              breaks = block_scope[KatakataIrb::Scope::BREAK_RESULT]
              if block_scope.terminated?
                [KatakataIrb::Types::UnionType[*nexts], breaks]
              else
                [KatakataIrb::Types::UnionType[result, *nexts], breaks]
              end
            end
          end
        else
          call_block_proc = ->(_block_args, _self_type) { KatakataIrb::Types::OBJECT }
        end
      end
      simulate_call receiver, method_name, args_type, kwargs_type(kwargs, scope), call_block_proc
    end
    if !optional_chain
      evaluate_method.call receiver, scope
    elsif receiver_type.nil?
      KatakataIrb::Types::NIL
    else
      result = scope.conditional { evaluate_method.call receiver.nonnillable, _1 }
      if receiver.nillable?
        KatakataIrb::Types::UnionType[result, KatakataIrb::Types::NIL]
      else
        result
      end
    end
  end

  def simulate_call(receiver, method_name, args, kwargs, block, name_match: true)
    methods = KatakataIrb::Types.rbs_methods receiver, method_name.to_sym, args, kwargs, !!block
    block_called = false
    type_breaks = methods.map do |method, given_params, method_params|
      receiver_vars = (receiver in KatakataIrb::Types::InstanceType) ? receiver.params : {}
      free_vars = method.type.free_variables - receiver_vars.keys.to_set
      vars = receiver_vars.merge KatakataIrb::Types.match_free_variables(free_vars, method_params, given_params)
      if block && method.block
        params_type = method.block.type.required_positionals.map do |func_param|
          KatakataIrb::Types.from_rbs_type func_param.type, receiver, vars
        end
        self_type = KatakataIrb::Types.from_rbs_type method.block.self_type, receiver, vars if method.block.self_type
        block_response, breaks = block.call params_type, self_type
        block_called = true
        vars.merge! KatakataIrb::Types.match_free_variables(free_vars - vars.keys.to_set, [method.block.type.return_type], [block_response])
      end
      [KatakataIrb::Types.from_rbs_type(method.type.return_type, receiver, vars || {}), breaks]
    end
    block&.call [], nil unless block_called
    types = type_breaks.map(&:first)
    breaks = type_breaks.map(&:last).compact
    types << OBJECT_METHODS[method_name.to_sym] if name_match && OBJECT_METHODS.has_key?(method_name.to_sym)

    if method_name.to_sym == :new
      receiver.types.each do |type|
        if (type in KatakataIrb::Types::SingletonType) && type.module_or_class.is_a?(Class)
          types << KatakataIrb::Types::InstanceType.new(type.module_or_class)
        end
      end
    end
    KatakataIrb::Types::UnionType[*types, *breaks]
  end

  def extract_param_names(params)
    params => [:params, pre_required, optional, rest, post_required, keywords, keyrest, block]
    names = []
    extract_mlhs = ->(item) do
      case item
      in [:var_field, [:@ident, name,],]
        names << name
      in [:@ident, name,]
        names << name
      in [:mlhs, *items]
        items.each(&extract_mlhs)
      in [:rest_param, item]
        extract_mlhs.call item if item
      in [:field | :aref_field,]
        # a.b, c[i] = value
      in [:excessed_comma]
      in [:args_forward]
      end
    end
    [*pre_required, *post_required].each(&extract_mlhs)
    extract_mlhs.call rest if rest
    optional&.each do |key, _value|
      key => [:@ident, name,]
      names << name
    end
    keywords&.each do |key, _value|
      key => [:@label, label,]
      names << label.delete(':')
    end
    if keyrest in [:kwrest_params, [:@ident, name,]]
      names << name
    end
    if block in [:blockarg, [:@ident, name,]]
      names << name
    end
    names
  end

  def evaluate_assign_params(params, values, scope)
    values = values.dup
    params => [:params, pre_required, optional, rest, post_required, _keywords, keyrest, block]
    size = (pre_required&.size || 0) + (optional&.size || 0) + (post_required&.size || 0) + (rest ? 1 : 0)
    values = sized_splat values.first, :to_ary, size if values.size == 1 && size >= 2
    pre_values = values.shift pre_required.size if pre_required
    post_values = values.pop post_required.size if post_required
    opt_values = values.shift optional.size if optional
    rest_values = values
    evaluate_massign pre_required, pre_values, scope if pre_required
    evaluate_massign optional.map(&:first), opt_values, scope if optional
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::InstanceType.new Array, Elem: KatakataIrb::Types::UnionType[*rest_values]
    end
    evaluate_massign post_required, post_values, scope if post_required
    # TODO: assign keywords
    if keyrest in [:kwrest_param, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::InstanceType.new Hash, K: KatakataIrb::Types::SYMBOL, V: KatakataIrb::Types::OBJECT
    end
    if block in [:blockarg, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::PROC
    end
  end

  def evaluate_param_defaults(params, scope)
    params => [:params, _pre_required, optional, rest, _post_required, keywords, keyrest, block]
    optional&.each do |item, value|
      item => [:@ident, name,]
      scope[name] = simulate_evaluate value, scope, context
    end
    if rest in [:rest_param, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::ARRAY
    end
    keywords&.each do |key, value|
      key => [:@label, label,]
      name = label.delete ':'
      scope[name] = value ? simulate_evaluate(value, scope, context) : KatakataIrb::Types::OBJECT
    end
    if keyrest in [:kwrest_param, [:@ident, name,]]
        scope[name] = KatakataIrb::Types::HASH
    end
    if block in [:blockarg, [:@ident, name,]]
      scope[name] = KatakataIrb::Types::PROC
    end
  end

  def self.calculate_binding_scope(binding, parents, target)
    dig_targets = DigTarget.new(parents, target) do |_types, scope|
      return scope
    end
    scope = KatakataIrb::Scope.from_binding(binding)
    new(dig_targets).simulate_evaluate parents[0], scope, {}
    scope
  end

  def self.calculate_receiver(binding, parents, receiver)
    dig_targets = DigTarget.new(parents, receiver) do |type, _scope|
      return type
    end
    lvars = binding.local_variables.to_h { [_1, binding.local_variable_get(_1)] }
    root = parents[0]
    if root in { type: :SCOPE }
      root.children[0].each do |lvar|
        lvars[lvar] ||= nil
      end
      root = root.children[2]
    end
    new(dig_targets).simulate_evaluate root, KatakataIrb::Scope.from_binding(binding, lvars), {}
    KatakataIrb::Types::NIL
  end
end
