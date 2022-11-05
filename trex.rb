module TRex
  def self.parse(tokens)
    opens = []
    pending_heredocs = []
    first_token_on_line = true
    tokens.each_with_index do |t, index|
      skip = false
      last_tok, state, args = opens.last
      case state
      when :in_unquoted_symbol
        opens.pop
        skip = true if %i[on_ident on_const on_op on_cvar on_ivar on_gvar on_kw on_int on_backtick].include? t.event
      when :in_method_head
        unless %i[on_sp on_ignored_nl].include?(t.event)
          next_args = []
          body = nil
          if args.include? :receiver
            case t.event
            when :on_lparen, :on_ivar, :on_gvar, :on_cvar
              next_args << :dot
            when :on_op, :on_kw
              skip = true
              next_args << :arg
            when :on_ident, :on_const
              next_args.push :arg, :dot
            end
          end
          if args.include? :dot
            next_args << :name if t.event == :on_period || (t.event == :on_op && t.tok == '::')
          end
          if args.include? :name
            if %i[on_ident on_const on_op on_kw].include? t.event
              next_args << :arg
              skip = true
            end
          end
          if args.include? :arg
            case t.event
            when :on_op
              body = :oneliner if t.tok == '='
            when :on_nl, :on_semicolon
              body = :normal
            when :on_lparen
              next_args << :eq
            else
              next_args << :arg_without_paren
            end
          end
          if args.include? :eq
            if t.event == :on_op && t.tok == '='
              body = :oneliner
            elsif t.event != :on_embdoc_beg
              body = :normal
            end
          end
          if args.include? :args_without_paren
            body = :normal if %i[on_semicolon on_nl].include? t.event
          end
          if body == :oneliner
            opens.pop
            opens << [last_tok, :in_oneliner_def]
          elsif body
            opens.pop
            opens << [last_tok, nil]
          else
            opens.pop
            opens << [last_tok, :in_method_head, next_args]
          end
        end
      when :in_oneliner_def
        if %i[on_semicolon on_nl on_rbrace on_rbracket on_rparen].include?(t.event) ||
          (t.event == :on_kw && t.tok == 'end') ||
          (t.event == :on_kw && %w[if unless while until].include?(t.tok) && t.state.allbits?(Ripper::EXPR_LABEL))
          opens.pop
        end
      when :in_for_while_condition
        if t.event == :on_semicolon || t.event == :on_nl || (t.event == :on_kw && t.tok == 'do')
          opens.pop
          opens << [last_tok, nil]
        end
      end

      unless skip
        case t.event
        when :on_kw
          case t.tok
          when 'begin', 'class', 'module', 'do', 'case'
            opens << [t, nil]
          when 'end'
            opens.pop
          when 'def'
            opens << [t, :in_method_head, [:receiver, :name]]
          when 'if', 'unless'
            unless t.state.allbits?(Ripper::EXPR_LABEL)
              opens << [t, nil]
            end
          when 'while', 'until'
            unless t.state.allbits?(Ripper::EXPR_LABEL)
              opens << [t, :in_while_until_condition]
            end
          when 'ensure', 'rescue'
            unless t.state.allbits?(Ripper::EXPR_LABEL)
              opens.pop
              opens << [t, nil]
            end
          when 'elsif', 'else', 'when'
            opens.pop
            opens << [t, nil]
          when 'for'
            opens << [t, :in_for_while_condition]
          when 'in'
            if last_tok&.event == :on_kw && %w[case in].include?(last_tok.tok) && first_token_on_line
              opens.pop
              opens << [t, nil]
            end
          end
        when :on_lparen, :on_lbracket, :on_lbrace, :on_tlambeg, :on_embexpr_beg, :on_embdoc_beg
          opens << [t, nil]
        when :on_rparen, :on_rbracket, :on_rbrace, :on_embexpr_end, :on_embdoc_end
          opens.pop
        when :on_heredoc_beg
          pending_heredocs << t
        when :on_heredoc_end
          opens.pop
        when :on_backtick
          opens << [t, nil] if t.state.allbits?(Ripper::EXPR_BEG)
        when :on_tstring_beg, :on_words_beg, :on_qwords_beg, :on_symbols_beg, :on_qsymbols_beg, :on_regexp_beg
          opens << [t, nil]
        when :on_tstring_end, :on_regexp_end, :on_label_end
          opens.pop
        when :on_symbeg
          if t.tok == ':'
            opens << [t, :in_unquoted_symbol]
          else
            opens << [t, nil]
          end
        end
      end
      if t.event == :on_nl || t.event == :on_semicolon
        first_token_on_line = true
      elsif t.event != :on_sp
        first_token_on_line = false
      end
      if pending_heredocs.any? && t.tok.include?("\n")
        pending_heredocs.reverse_each { opens << [_1, nil] }
        pending_heredocs = []
      end
      yield t, index, opens if block_given?
    end
    [opens, pending_heredocs.reverse]
  end

  def self.parse_line(tokens)
    line_tokens = []
    prev_opens = []
    min_depth = 0
    output = []
    last_opens, unclosed_heredocs = TRex.parse(tokens) do |t, _index, opens|
      depth = t == opens.last&.first ? opens.size - 1 : opens.size
      min_depth = depth if depth < min_depth
      if t.tok.include? "\n"
        t.tok.each_line do |line|
          line_tokens << [t, line]
          next if line[-1] != "\n"
          next_opens = opens.dup
          output << [line_tokens, prev_opens, next_opens, min_depth]
          prev_opens = next_opens
          min_depth = prev_opens.size
          line_tokens = []
        end
      else
        line_tokens << [t, t.tok]
      end
    end
    output << [line_tokens, prev_opens, last_opens, min_depth] if line_tokens.any?
    [output, unclosed_heredocs]
  end
end
