module KatakataIrb; end
module KatakataIrb::TRex
  def self.interpolate_ripper_ignored_tokens(code, tokens)
    line_positions = code.lines.reduce([0]) { _1 << _1.last + _2.bytesize }
    prev_byte_pos = 0
    interpolated = []
    prev_line = 1
    event = :on_ignored_by_ripper
    tokens.each do |t|
      line, col = t.pos
      byte_pos = line_positions[line - 1] + col
      if prev_byte_pos < byte_pos
        tok = code.byteslice(prev_byte_pos...byte_pos)
        pos = [prev_line, prev_byte_pos - line_positions[prev_line - 1]]
        interpolated << Ripper::Lexer::Elem.new(pos, event, tok, 0)
        prev_line += tok.count("\n")
      end
      interpolated << t
      prev_byte_pos = byte_pos + t.tok.bytesize
      prev_line += t.tok.count("\n")
    end
    if prev_byte_pos < code.bytesize
      tok = code.byteslice(prev_byte_pos..)
      pos = [prev_line, prev_byte_pos - line_positions[prev_line - 1]]
      interpolated << Ripper::Lexer::Elem.new(pos, event, tok, 0)
    end
    interpolated
  end

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
        skip = true if %i[on_ident on_const on_op on_cvar on_ivar on_gvar on_kw on_int on_backtick].include?(t.event)
      when :in_method_head
        unless %i[on_sp on_ignored_nl on_comment on_embdoc_beg on_embdoc on_embdoc_end].include?(t.event)
          next_args = []
          body = nil
          if args.include?(:receiver)
            case t.event
            when :on_lparen, :on_ivar, :on_gvar, :on_cvar
              # def (receiver). | def @ivar. | def $gvar. | def @@cvar.
              next_args << :dot
            when :on_kw
              case t.tok
              when 'self', 'true', 'false', 'nil'
                # def self(arg) | def self.
                next_args.push(:arg, :dot)
              else
                # def if(arg)
                skip = true
                next_args << :arg
              end
            when :on_op, :on_backtick
              # def +(arg)
              skip = true
              next_args << :arg
            when :on_ident, :on_const
              # def a(arg) | def a.
              next_args.push(:arg, :dot)
            end
          end
          if args.include?(:dot)
            # def receiver.name
            next_args << :name if t.event == :on_period || (t.event == :on_op && t.tok == '::')
          end
          if args.include?(:name)
            if %i[on_ident on_const on_op on_kw on_backtick].include?(t.event)
              # def name(arg) | def receiver.name(arg)
              next_args << :arg
              skip = true
            end
          end
          if args.include?(:arg)
            case t.event
            when :on_nl, :on_semicolon
              # def recever.f;
              body = :normal
            when :on_lparen
              # def recever.f()
              next_args << :eq
            else
              if t.event == :on_op && t.tok == '='
                # def receiver.f =
                body = :oneliner
              else
                # def recever.f arg
                next_args << :arg_without_paren
              end
            end
          end
          if args.include?(:eq)
            if t.event == :on_op && t.tok == '='
              body = :oneliner
            else
              body = :normal
            end
          end
          if args.include?(:arg_without_paren)
            if %i[on_semicolon on_nl].include?(t.event)
              # def f a;
              body = :normal
            else
              # def f a, b
              next_args << :arg_without_paren
            end
          end
          if body == :oneliner
            opens.pop
          elsif body
            opens[-1] = [last_tok, nil]
          else
            opens[-1] = [last_tok, :in_method_head, next_args]
          end
        end
      when :in_for_while_until_condition
        if t.event == :on_semicolon || t.event == :on_nl || (t.event == :on_kw && t.tok == 'do')
          skip = true if t.event == :on_kw && t.tok == 'do'
          opens[-1] = [last_tok, nil]
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
              opens << [t, :in_for_while_until_condition]
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
            opens << [t, :in_for_while_until_condition]
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
    opens.map(&:first) + pending_heredocs.reverse
  end

  def self.parse_line(tokens)
    line_tokens = []
    prev_opens = []
    min_depth = 0
    output = []
    last_opens = parse(tokens) do |t, _index, opens|
      depth = t == opens.last&.first ? opens.size - 1 : opens.size
      min_depth = depth if depth < min_depth
      if t.tok.include?("\n")
        t.tok.each_line do |line|
          line_tokens << [t, line]
          next if line[-1] != "\n"
          next_opens = opens.map(&:first)
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
    output
  end
end
