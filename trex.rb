module TRex
  def self.parse(tokens)
    opens = []
    pending_heredocs = []
    tokens.each_with_index do |t, index|
      skip = false
      last_tok, state = opens.last 
      case state
      when :in_unquoted_symbol
        opens.pop
        skip = true if %i[on_ident on_const on_op on_cvar on_ivar on_gvar on_kw on_int on_backtick].include? t.event
      when :in_method_receiver_name
        if %i[on_kw on_op].include?(t.event)
          skip = true
          opens.pop
          opens << [last_tok, :in_method_args]
        elsif %i[on_ident on_const].include?(t.event)
          skip = true
          opens.pop
          opens << [last_tok, :in_method_dot_or_args]
        elsif t.event == :on_lparen
          opens.pop
          opens << [last_tok, :in_method_dot_or_args]
        end
      when :in_method_dot_or_args
        if t.state.allbits?(Ripper::EXPR_DOT)
          skip = true
          opens.pop
          opens << [last_tok, :in_method_name]
        elsif t.event == :on_lparen
          opens.pop
          opens << [last_tok, :in_method_args]
        elsif !%i[on_nl on_sp].include?(t.event)
          opens.pop
          opens << [last_tok, :in_method_args_without_parenthesis]
        end
      when :in_method_name
        if %i[on_kw on_op on_ident on_const].include?(t.event)
          skip = true
          opens.pop
          opens << [last_tok, :in_method_args]
        elsif !%w[on_ignored_nl on_sp on_lparen on_period].include?(t.event) && !(t.event == :on_op && t.tok == '::') && !t.state.allbits?(Ripper::EXPR_FNAME)
          opens.pop
          opens << [last_tok, :in_method_args]
        end
      when :in_method_args
        if t.event == :on_op && t.tok == '='
          skip = true
          opens.pop
          opens << [last_tok, :in_oneliner_def]
        elsif %i[on_op on_label on_ident].include? t.event
          opens.pop
          opens << [last_tok, :in_method_args_without_parenthesis]
        end
      when :in_method_args_without_parenthesis
        if %i[on_semicolon on_nl].include? t.event
          opens.pop
          opens << last_tok
        end
      when :in_oneliner_def
        if %i[on_semicolon on_nl on_rbrace on_rbracket on_rparen].include? t.event
          opens.pop
        end
      when :in_for_while_condition
        if t.event == :on_semicolon || t.evnet == :on_nl || (t.event == :on_kw && t.tok == 'do')
          opens.pop
          opens << last_tok
        end
      end

      unless skip
        case t.event
        when :on_kw
          case t.tok
          when 'begin', 'class', 'module', 'do', 'case'
            opens << t
          when 'end'
            opens.pop
          when 'def'
            opens << [t, :in_method_receiver_name]
          when 'if', 'unless'
            unless t.state.allbits?(Ripper::EXPR_LABEL)
              opens << t
            end
          when 'while', 'until'
            unless t.state.allbits?(Ripper::EXPR_LABEL)
              opens << [t, :in_while_until_condition]
            end
          when 'ensure', 'rescue'
            unless t.state.allbits?(Ripper::EXPR_LABEL)
              opens.pop
              opens << t
            end
          when 'elsif', 'else', 'when'
            opens.pop
            opens << t
          when 'for'
            opens << [t, :in_for_while_condition]
          when 'in'
            if last_tok&.event == :on_kw
              if %w[when in case].include?(last_tok.tok)
                opens.pop
                opens << t
              end
            end
          end
        when :on_lparen, :on_lbracket, :on_lbrace, :on_tlambeg, :on_embexpr_beg
          opens << t
        when :on_rparen, :on_rbracket, :on_rbrace, :on_embexpr_end
          opens.pop
        when :on_heredoc_beg
          pending_heredocs << t
        when :on_heredoc_end
          opens.pop
        when :on_backtick
          opens << t if t.state.allbits?(Ripper::EXPR_BEG)
        when :on_tstring_beg, :on_words_beg, :on_qwords_beg, :on_symbols_beg, :on_qsymbols_beg, :on_regexp_beg
          opens << t
        when :on_tstring_end, :on_regexp_end, :on_label_end
          opens.pop
        when :on_symbeg
          if t.tok == ':'
            opens << [t, :in_unquoted_symbol]
          else
            opens << t
          end
        end
      end
      if pending_heredocs.any? && t.tok.include?("\n")
        opens.concat(pending_heredocs.reverse)
        pending_heredocs = []
      end
      yield t, index, opens
    end
    opens + pending_heredocs.reverse
  end

  def self.parse_line(tokens)
    line_tokens = []
    prev_opens = []
    min_depth = 0
    output = []
    last_opens = TRex.parse(tokens) do |t, _index, opens|
      depth = t == opens.last ? opens.size - 1 : opens.size
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
    output << [line_tokens, prev_opens, last_opens, min_depth]
    output
  end
end
