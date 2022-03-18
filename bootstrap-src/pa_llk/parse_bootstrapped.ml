
open Pcaml

open Llk_types
open Llk_regexps
open Parse_gram
open Print_gram

let expr_LEVEL_simple = expr

module LLKGram =
  struct
    let gram = Pcaml.gram
    let lexer = Grammar.glexer gram
    module F =
      struct
        open Pa_llk_runtime.Llk_runtime
        let rec assoc __strm__ =
          match assoc_matcher __strm__ with
            0 -> (parser [< '"UIDENT", "LEFTA" >] -> LEFTA) __strm__
          | 1 -> (parser [< '"UIDENT", "NONA" >] -> NONA) __strm__
          | 2 -> (parser [< '"UIDENT", "RIGHTA" >] -> RIGHTA) __strm__
          | _ -> raise Stream.Failure
        and assoc_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEFTA") -> 0
          | Some ("UIDENT", "NONA") -> 1
          | Some ("UIDENT", "RIGHTA") -> 2
          | _ -> raise Stream.Failure
        and bootstrapped_top =
          parser
            [< '"", "GRAMMAR"; e = grammar_body; '"", "END"; '"", ";";
               '"EOI", _ >] ->
              norm_top e
        and bootstrapped_top_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "GRAMMAR") -> 0
          | _ -> raise Stream.Failure
        and e0 __strm__ =
          match e0_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "#"; '"INT", x >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   Output (loc, int_of_string x))
                __strm__
          | 1 ->
              (parser bp
                 [< '"", "$"; '"LIDENT", x >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   Anti (loc, x))
                __strm__
          | 2 -> (parser [< '"", "("; x = e6; '"", ")" >] -> x) __strm__
          | 3 ->
              (parser bp
                 [< '"", "eps" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in EPS loc)
                __strm__
          | 4 ->
              (parser bp
                 [< '"LIDENT", x >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ID (loc, x))
                __strm__
          | 5 ->
              (parser bp
                 [< '"STRING", x >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   Special (loc, x))
                __strm__
          | 6 -> (parser [< '"UIDENT", x; a = e0__00 x >] -> a) __strm__
          | _ -> raise Stream.Failure
        and e0_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "#") -> 0
          | Some ("", "$") -> 1
          | Some ("", "(") -> 2
          | Some ("", "eps") -> 3
          | Some ("LIDENT", _) -> 4
          | Some ("STRING", _) -> 5
          | Some ("UIDENT", _) -> 6
          | _ -> raise Stream.Failure
        and e0__00 x __strm__ =
          match e0__00_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "/"; '"STRING", s >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   Class (loc, x, Some s))
                __strm__
          | 1 ->
              (parser bp
                 [< >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   Class (loc, x, None))
                __strm__
          | _ -> raise Stream.Failure
        and e0__00_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "/") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "#") -> 1
          | Some ("", "$") -> 1
          | Some ("", "&") -> 1
          | Some ("", "(") -> 1
          | Some ("", ")") -> 1
          | Some ("", "*") -> 1
          | Some ("", ";") -> 1
          | Some ("", "?") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | Some ("", "~") -> 1
          | _ -> raise Stream.Failure
        and e1 = parser [< x = e0; a = e1__01 x >] -> a
        and e1_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "eps") -> 0
          | _ -> raise Stream.Failure
        and e1__01 x __strm__ =
          match e1__01_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "*" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   STAR (loc, x))
                __strm__
          | 1 -> (parser [< >] -> x) __strm__
          | _ -> raise Stream.Failure
        and e1__01_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "*") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "#") -> 1
          | Some ("", "$") -> 1
          | Some ("", "&") -> 1
          | Some ("", "(") -> 1
          | Some ("", ")") -> 1
          | Some ("", ";") -> 1
          | Some ("", "?") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | Some ("", "~") -> 1
          | _ -> raise Stream.Failure
        and e2 __strm__ =
          match e2_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "~"; x = e2' >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   NEG (loc, x))
                __strm__
          | 1 -> (parser [< a = e2' >] -> a) __strm__
          | _ -> raise Stream.Failure
        and e2_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "~") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "#") -> 1
          | Some ("", "$") -> 1
          | Some ("", "(") -> 1
          | Some ("", "eps") -> 1
          | _ -> raise Stream.Failure
        and e2' = parser [< x = e1; a = e2'__02 x >] -> a
        and e2'_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "eps") -> 0
          | _ -> raise Stream.Failure
        and e2'__02 x __strm__ =
          match e2'__02_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "?" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   OPT (loc, x))
                __strm__
          | 1 -> (parser [< >] -> x) __strm__
          | _ -> raise Stream.Failure
        and e2'__02_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "?") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "#") -> 1
          | Some ("", "$") -> 1
          | Some ("", "&") -> 1
          | Some ("", "(") -> 1
          | Some ("", ")") -> 1
          | Some ("", ";") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | Some ("", "~") -> 1
          | _ -> raise Stream.Failure
        and e3 =
          parser bp
            [< l = parse_list1 e2 >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in CONC (loc, l)
        and e3_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "eps") -> 0
          | Some ("", "~") -> 0
          | _ -> raise Stream.Failure
        and e4 =
          parser bp
            [< l =
                 parse_list1_with_sep e3
                   (parser [< '"", "&" >] -> ()) >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in CONJ (loc, l)
        and e4_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "eps") -> 0
          | Some ("", "~") -> 0
          | _ -> raise Stream.Failure
        and e5 =
          parser bp
            [< l =
                 parse_list1_with_sep e4
                   (parser [< '"", "|" >] -> ()) >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in DISJ (loc, l)
        and e5_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "eps") -> 0
          | Some ("", "~") -> 0
          | _ -> raise Stream.Failure
        and e6 __strm__ =
          match e6_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "let"; '"LIDENT", s; '"", "="; re1 = e5; '"", "in";
                    re2 = e5 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   LETIN (loc, s, re1, re2))
                __strm__
          | 1 -> (parser [< a = e5 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and e6_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "let") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "#") -> 1
          | Some ("", "$") -> 1
          | Some ("", "(") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "~") -> 1
          | _ -> raise Stream.Failure
        and entry =
          parser bp
            [< '"LIDENT", n; formals = entry__03; '"", ":";
               pos = parse_opt position; ll = level_list >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              {ae_loc = loc; ae_formals = formals; ae_name = n; ae_pos = pos;
               ae_levels = ll}
        and entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and entry__03 __strm__ =
          match entry__03_matcher __strm__ with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      parse_list1_with_sep
                        (Grammar.Entry.parse_token_stream patt)
                        (parser [< '"", "," >] -> ());
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and entry__03_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("", ":") -> 1
          | _ -> raise Stream.Failure
        and exports =
          parser
            [< '"UIDENT", "EXPORT"; '"", ":";
               sl = parse_list1 (parser [< '"LIDENT", __x__ >] -> __x__);
               '"", ";" >] ->
              sl
        and exports_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "EXPORT") -> 0
          | _ -> raise Stream.Failure
        and external_entry =
          parser
            [< '"", "external"; '"LIDENT", s; '"", ":";
               '"UIDENT", "PREDICTION"; r = regexp; '"", ";" >] ->
              s, r
        and external_entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | _ -> raise Stream.Failure
        and externals = parser [< a = parse_list1 external_entry >] -> a
        and externals_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | _ -> raise Stream.Failure
        and grammar_body =
          parser bp
            [< '"UIDENT", gid; '"", ":";
               extend_opt = parse_opt grammar_body__04;
               expl = grammar_body__05; rl = grammar_body__06;
               extl = grammar_body__07;
               el = parse_list1 grammar_body__08 >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              {gram_loc = loc; gram_extend = extend_opt; gram_id = gid;
               gram_exports = expl; gram_external_asts = extl;
               gram_regexp_asts = rl; gram_entries = el}
        and grammar_body_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and grammar_body__04 =
          parser
            [< '"", "EXTEND";
               id = Grammar.Entry.parse_token_stream longident_lident;
               '"", ";" >] ->
              id
        and grammar_body__04_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "EXTEND") -> 0
          | _ -> raise Stream.Failure
        and grammar_body__05 __strm__ =
          match grammar_body__05_matcher __strm__ with
            0 -> (parser [< a = exports >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__05_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "EXPORT") -> 0
          | Some ("UIDENT", "REGEXPS") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ -> raise Stream.Failure
        and grammar_body__06 __strm__ =
          match grammar_body__06_matcher __strm__ with
            0 -> (parser [< a = regexps >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__06_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "REGEXPS") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ -> raise Stream.Failure
        and grammar_body__07 __strm__ =
          match grammar_body__07_matcher __strm__ with
            0 -> (parser [< a = externals >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__07_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | Some ("LIDENT", _) -> 1
          | _ -> raise Stream.Failure
        and grammar_body__08 = parser [< e = entry; '"", ";" >] -> e
        and grammar_body__08_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and level =
          parser bp
            [< lab = parse_opt (parser [< '"STRING", __x__ >] -> __x__);
               ass = parse_opt assoc; rules = rule_list >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              {al_loc = loc; al_label = lab; al_assoc = ass; al_rules = rules}
        and level_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEFTA") -> 0
          | Some ("UIDENT", "NONA") -> 0
          | Some ("UIDENT", "RIGHTA") -> 0
          | Some ("STRING", _) -> 0
          | Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and level_list =
          parser
            [< '"", "[";
               ll = parse_list0_with_sep level (parser [< '"", "|" >] -> ());
               '"", "]" >] ->
              ll
        and level_list_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and paren_pattern =
          parser bp
            [< '"", "(";
               l = parse_list1_with_sep pattern (parser [< '"", "," >] -> ());
               '"", ")" >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              MLast.PaTup (loc, Ploc.VaVal l)
        and paren_pattern_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | _ -> raise Stream.Failure
        and pattern __strm__ =
          match pattern_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "_" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   MLast.PaAny loc)
                __strm__
          | 1 ->
              (parser bp
                 [< '"LIDENT", i >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   MLast.PaLid (loc, Ploc.VaVal i))
                __strm__
          | 2 -> (parser [< a = paren_pattern >] -> a) __strm__
          | _ -> raise Stream.Failure
        and pattern_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "_") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("", "(") -> 2
          | _ -> raise Stream.Failure
        and position __strm__ =
          match position_matcher __strm__ with
            0 ->
              (parser [< '"UIDENT", "AFTER"; '"STRING", n >] -> POS_AFTER n)
                __strm__
          | 1 ->
              (parser [< '"UIDENT", "BEFORE"; '"STRING", n >] -> POS_BEFORE n)
                __strm__
          | 2 -> (parser [< '"UIDENT", "FIRST" >] -> POS_FIRST) __strm__
          | 3 -> (parser [< '"UIDENT", "LAST" >] -> POS_LAST) __strm__
          | 4 ->
              (parser [< '"UIDENT", "LEVEL"; '"STRING", n >] -> POS_LEVEL n)
                __strm__
          | 5 ->
              (parser [< '"UIDENT", "LIKE"; '"STRING", n >] -> POS_LIKE n)
                __strm__
          | _ -> raise Stream.Failure
        and position_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "AFTER") -> 0
          | Some ("UIDENT", "BEFORE") -> 1
          | Some ("UIDENT", "FIRST") -> 2
          | Some ("UIDENT", "LAST") -> 3
          | Some ("UIDENT", "LEVEL") -> 4
          | Some ("UIDENT", "LIKE") -> 5
          | _ -> raise Stream.Failure
        and psymbol __strm__ =
          match
            psymbol_regexp __strm__[@llk.regexp "\"_\" #0 | LIDENT \"=\" #1 | LIDENT \"[\" #2 | \"(\" (LIDENT | \"(\" | \"_\" | \",\" | \")\")* \"=\" #3 | (LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\" | UIDENT \"V\") #4"]
          with
            Some (_, 0) ->
              (parser bp
                 [< '"", "_"; '"", "="; s = symbol >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc; ap_patt = Some (MLast.PaAny loc);
                    ap_symb = s})
                __strm__
          | Some (_, 1) ->
              (parser bp
                 [< '"LIDENT", p; '"", "="; s = symbol >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc;
                    ap_patt = Some (MLast.PaLid (loc, Ploc.VaVal p));
                    ap_symb = s})
                __strm__
          | Some (_, 2) ->
              (parser bp
                 [< '"LIDENT", p; args = psymbol__09;
                    lev = parse_opt psymbol__10 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc; ap_patt = None;
                    ap_symb = ASnterm (loc, p, args, lev)})
                __strm__
          | Some (_, 3) ->
              (parser bp
                 [< p = paren_pattern; '"", "="; s = symbol >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc; ap_patt = Some p; ap_symb = s})
                __strm__
          | Some (_, 4) ->
              (parser bp
                 [< s = symbol >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc; ap_patt = None; ap_symb = s})
                __strm__
          | _ -> raise Stream.Failure
        and psymbol_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            match must_peek_nth (ofs + 1) strm with
              Some ("", "(") -> q0003 lastf (ofs + 1)
            | Some ("", "[") -> q0002 lastf (ofs + 1)
            | Some ("", "_") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "FLAG") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "LEFT_ASSOC") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "LIST0") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "LIST1") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "NEXT") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "OPT") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "PREDICT") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "SELF") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "V") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("LIDENT", _) -> q0006 lastf (ofs + 1)
            | Some ("STRING", _) -> q0002 lastf (ofs + 1)
            | Some ("UIDENT", _) -> q0002 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 0) in lastf
          and q0002 lastf ofs = let lastf = Some (ofs, 4) in lastf
          and q0003 lastf ofs =
            let lastf = Some (ofs, 4) in
            match must_peek_nth (ofs + 1) strm with
              Some ("", "(") -> q0004 lastf (ofs + 1)
            | Some ("", ")") -> q0004 lastf (ofs + 1)
            | Some ("", ",") -> q0004 lastf (ofs + 1)
            | Some ("", "=") -> q0005 lastf (ofs + 1)
            | Some ("", "_") -> q0004 lastf (ofs + 1)
            | Some ("LIDENT", _) -> q0004 lastf (ofs + 1)
            | _ -> lastf
          and q0004 lastf ofs =
            match must_peek_nth (ofs + 1) strm with
              Some ("", "(") -> q0004 lastf (ofs + 1)
            | Some ("", ")") -> q0004 lastf (ofs + 1)
            | Some ("", ",") -> q0004 lastf (ofs + 1)
            | Some ("", "=") -> q0005 lastf (ofs + 1)
            | Some ("", "_") -> q0004 lastf (ofs + 1)
            | Some ("LIDENT", _) -> q0004 lastf (ofs + 1)
            | _ -> lastf
          and q0005 lastf ofs = let lastf = Some (ofs, 3) in lastf
          and q0006 lastf ofs =
            let lastf = Some (ofs, 4) in
            match must_peek_nth (ofs + 1) strm with
              Some ("", "=") -> q0008 lastf (ofs + 1)
            | Some ("", "[") -> q0007 lastf (ofs + 1)
            | _ -> lastf
          and q0007 lastf ofs = let lastf = Some (ofs, 2) in lastf
          and q0008 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and psymbol__09 __strm__ =
          match psymbol__09_matcher __strm__ with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      parse_list1_with_sep
                        (Grammar.Entry.parse_token_stream expr)
                        (parser [< '"", "," >] -> ());
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and psymbol__09_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("UIDENT", "LEVEL") -> 1
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and psymbol__10 = parser [< '"UIDENT", "LEVEL"; '"STRING", s >] -> s
        and psymbol__10_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | _ -> raise Stream.Failure
        and regexp = parser [< a = e6 >] -> a
        and regexp_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "eps") -> 0
          | Some ("", "let") -> 0
          | Some ("", "~") -> 0
          | _ -> raise Stream.Failure
        and regexp_entry =
          parser [< '"LIDENT", n; '"", "="; r = regexp; '"", ";" >] -> n, r
        and regexp_entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and regexps =
          parser
            [< '"UIDENT", "REGEXPS"; '"", ":"; rl = parse_list1 regexp_entry;
               '"", "END"; '"", ";" >] ->
              rl
        and regexps_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "REGEXPS") -> 0
          | _ -> raise Stream.Failure
        and rule __strm__ =
          match rule_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "->";
                    act = Grammar.Entry.parse_token_stream expr >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ar_loc = loc; ar_psymbols = []; ar_action = Some act})
                __strm__
          | 1 ->
              (parser
                 [< psl =
                      parse_list1_with_sep psymbol
                        (parser [< '"", ";" >] -> ());
                    a = rule__11 psl >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and rule_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "->") -> 0
          | Some ("UIDENT", "FLAG") -> 1
          | Some ("UIDENT", "LEFT_ASSOC") -> 1
          | Some ("UIDENT", "LIST0") -> 1
          | Some ("UIDENT", "LIST1") -> 1
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "OPT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "SELF") -> 1
          | Some ("UIDENT", "V") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "(") -> 1
          | Some ("", "[") -> 1
          | Some ("", "_") -> 1
          | _ -> raise Stream.Failure
        and rule__11 psl __strm__ =
          match rule__11_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "->";
                    act = Grammar.Entry.parse_token_stream expr >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ar_loc = loc; ar_psymbols = psl; ar_action = Some act})
                __strm__
          | 1 ->
              (parser bp
                 [< >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ar_loc = loc; ar_psymbols = psl; ar_action = None})
                __strm__
          | _ -> raise Stream.Failure
        and rule__11_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "->") -> 0
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and rule_list = parser [< '"", "["; a = rule_list__12 >] -> a
        and rule_list_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and rule_list__12 __strm__ =
          match rule_list__12_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {au_loc = loc; au_rules = []})
                __strm__
          | 1 ->
              (parser bp
                 [< rules =
                      parse_list1_with_sep rule (parser [< '"", "|" >] -> ());
                    '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {au_loc = loc; au_rules = rules})
                __strm__
          | _ -> raise Stream.Failure
        and rule_list__12_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "]") -> 0
          | Some ("UIDENT", "FLAG") -> 1
          | Some ("UIDENT", "LEFT_ASSOC") -> 1
          | Some ("UIDENT", "LIST0") -> 1
          | Some ("UIDENT", "LIST1") -> 1
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "OPT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "SELF") -> 1
          | Some ("UIDENT", "V") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "(") -> 1
          | Some ("", "->") -> 1
          | Some ("", "[") -> 1
          | Some ("", "_") -> 1
          | _ -> raise Stream.Failure
        and sep_opt_sep =
          parser
            [< '"UIDENT", ("SEP" as sep); t = symbol;
               b = parse_flag sep_opt_sep__13 >] ->
              t, b
        and sep_opt_sep_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "SEP") -> 0
          | _ -> raise Stream.Failure
        and sep_opt_sep__13 = parser [< '"UIDENT", "OPT_SEP" >] -> ()
        and sep_opt_sep__13_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "OPT_SEP") -> 0
          | _ -> raise Stream.Failure
        and symbol = parser [< a = symbol__0001 >] -> a
        and symbol_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 0
          | Some ("UIDENT", "LIST0") -> 0
          | Some ("UIDENT", "LIST1") -> 0
          | Some ("UIDENT", "NEXT") -> 0
          | Some ("UIDENT", "OPT") -> 0
          | Some ("UIDENT", "PREDICT") -> 0
          | Some ("UIDENT", "SELF") -> 0
          | Some ("UIDENT", "V") -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and symbol__0001 __strm__ =
          match symbol__0001_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"UIDENT", "FLAG"; s = symbol__0002 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASflag (loc, s))
                __strm__
          | 1 ->
              (parser bp
                 [< '"UIDENT", "LEFT_ASSOC"; s1 = symbol__0002;
                    '"UIDENT", "ACCUMULATE"; s2 = symbol__0002;
                    '"UIDENT", "WITH";
                    e =
                      Grammar.Entry.parse_token_stream
                        expr_LEVEL_simple >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASleft_assoc (loc, s1, s2, e))
                __strm__
          | 2 ->
              (parser bp
                 [< '"UIDENT", "LIST0"; s = symbol__0002;
                    sep = parse_opt sep_opt_sep >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASlist (loc, LML_0, s, sep))
                __strm__
          | 3 ->
              (parser bp
                 [< '"UIDENT", "LIST1"; s = symbol__0002;
                    sep = parse_opt sep_opt_sep >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASlist (loc, LML_1, s, sep))
                __strm__
          | 4 ->
              (parser bp
                 [< '"UIDENT", "OPT"; s = symbol__0002 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASopt (loc, s))
                __strm__
          | 5 -> (parser [< a = symbol__0002 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 1
          | Some ("UIDENT", "LIST0") -> 2
          | Some ("UIDENT", "LIST1") -> 3
          | Some ("UIDENT", "OPT") -> 4
          | Some ("UIDENT", "NEXT") -> 5
          | Some ("UIDENT", "PREDICT") -> 5
          | Some ("UIDENT", "SELF") -> 5
          | Some ("UIDENT", "V") -> 5
          | Some ("LIDENT", _) -> 5
          | Some ("STRING", _) -> 5
          | Some ("UIDENT", _) -> 5
          | Some ("", "(") -> 5
          | Some ("", "[") -> 5
          | _ -> raise Stream.Failure
        and symbol__0002 __strm__ =
          match symbol__0002_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"UIDENT", "V"; s = symbol__0003;
                    al =
                      parse_list0
                        (parser [< '"STRING", __x__ >] -> __x__) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASvala (loc, s, al))
                __strm__
          | 1 -> (parser [< a = symbol__0003 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "V") -> 0
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "SELF") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "(") -> 1
          | Some ("", "[") -> 1
          | _ -> raise Stream.Failure
        and symbol__0003 __strm__ =
          match symbol__0003_matcher __strm__ with
            0 ->
              (parser [< '"", "("; s_t = symbol__0001; '"", ")" >] -> s_t)
                __strm__
          | 1 ->
              (parser bp
                 [< '"", "[";
                    rl =
                      parse_list0_with_sep rule (parser [< '"", "|" >] -> ());
                    '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASrules (loc, {au_loc = loc; au_rules = rl}))
                __strm__
          | 2 ->
              (parser bp
                 [< '"UIDENT", "NEXT"; args = symbol__0003__14 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASnext (loc, args))
                __strm__
          | 3 ->
              (parser bp
                 [< '"UIDENT", "PREDICT"; '"LIDENT", id >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASregexp (loc, id))
                __strm__
          | 4 ->
              (parser bp
                 [< '"UIDENT", "SELF"; args = symbol__0003__15 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASself (loc, args))
                __strm__
          | 5 ->
              (parser bp
                 [< '"STRING", e >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASkeyw (loc, e))
                __strm__
          | 6 ->
              (parser bp
                 [< '"LIDENT", id; args = symbol__0003__16;
                    lev = parse_opt symbol__0003__17 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASnterm (loc, id, args, lev))
                __strm__
          | 7 ->
              (parser [< '"UIDENT", x; a = symbol__0003__18 x >] -> a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | Some ("", "[") -> 1
          | Some ("UIDENT", "NEXT") -> 2
          | Some ("UIDENT", "PREDICT") -> 3
          | Some ("UIDENT", "SELF") -> 4
          | Some ("STRING", _) -> 5
          | Some ("LIDENT", _) -> 6
          | Some ("UIDENT", _) -> 7
          | _ -> raise Stream.Failure
        and symbol__0003__14 __strm__ =
          match symbol__0003__14_matcher __strm__ with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      parse_list1_with_sep
                        (Grammar.Entry.parse_token_stream expr)
                        (parser [< '"", "," >] -> ());
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0003__14_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("UIDENT", "ACCUMULATE") -> 1
          | Some ("UIDENT", "OPT_SEP") -> 1
          | Some ("UIDENT", "SEP") -> 1
          | Some ("UIDENT", "WITH") -> 1
          | Some ("STRING", _) -> 1
          | Some ("", ")") -> 1
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and symbol__0003__15 __strm__ =
          match symbol__0003__15_matcher __strm__ with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      parse_list1_with_sep
                        (Grammar.Entry.parse_token_stream expr)
                        (parser [< '"", "," >] -> ());
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0003__15_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("UIDENT", "ACCUMULATE") -> 1
          | Some ("UIDENT", "OPT_SEP") -> 1
          | Some ("UIDENT", "SEP") -> 1
          | Some ("UIDENT", "WITH") -> 1
          | Some ("STRING", _) -> 1
          | Some ("", ")") -> 1
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and symbol__0003__16 __strm__ =
          match symbol__0003__16_matcher __strm__ with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      parse_list1_with_sep
                        (Grammar.Entry.parse_token_stream expr)
                        (parser [< '"", "," >] -> ());
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0003__16_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("UIDENT", "ACCUMULATE") -> 1
          | Some ("UIDENT", "LEVEL") -> 1
          | Some ("UIDENT", "OPT_SEP") -> 1
          | Some ("UIDENT", "SEP") -> 1
          | Some ("UIDENT", "WITH") -> 1
          | Some ("STRING", _) -> 1
          | Some ("", ")") -> 1
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and symbol__0003__17 =
          parser [< '"UIDENT", "LEVEL"; '"STRING", s >] -> s
        and symbol__0003__17_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | _ -> raise Stream.Failure
        and symbol__0003__18 x __strm__ =
          match symbol__0003__18_matcher __strm__ with
            0 ->
              (parser bp
                 [< '"", "/"; '"STRING", e >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   AStok (loc, x, Some (Scanf.unescaped e)))
                __strm__
          | 1 ->
              (parser bp
                 [< >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   AStok (loc, x, None))
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0003__18_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "/") -> 0
          | Some ("UIDENT", "ACCUMULATE") -> 1
          | Some ("UIDENT", "OPT_SEP") -> 1
          | Some ("UIDENT", "SEP") -> 1
          | Some ("UIDENT", "WITH") -> 1
          | Some ("STRING", _) -> 1
          | Some ("", ")") -> 1
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
      end
    open Plexing
    let _ =
      lexer.tok_using ("EOI", "");
      lexer.tok_using ("INT", "");
      lexer.tok_using ("LIDENT", "");
      lexer.tok_using ("STRING", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("", "#");
      lexer.tok_using ("", "$");
      lexer.tok_using ("", "&");
      lexer.tok_using ("", "(");
      lexer.tok_using ("", ")");
      lexer.tok_using ("", "*");
      lexer.tok_using ("", ",");
      lexer.tok_using ("", "->");
      lexer.tok_using ("", "/");
      lexer.tok_using ("", ":");
      lexer.tok_using ("", ";");
      lexer.tok_using ("", "=");
      lexer.tok_using ("", "?");
      lexer.tok_using ("", "END");
      lexer.tok_using ("", "EXTEND");
      lexer.tok_using ("", "GRAMMAR");
      lexer.tok_using ("", "[");
      lexer.tok_using ("", "]");
      lexer.tok_using ("", "_");
      lexer.tok_using ("", "eps");
      lexer.tok_using ("", "external");
      lexer.tok_using ("", "in");
      lexer.tok_using ("", "let");
      lexer.tok_using ("", "|");
      lexer.tok_using ("", "~");
      ()
    let bootstrapped_top =
      Grammar.Entry.of_parser gram "bootstrapped_top" F.bootstrapped_top
  end

let pa (loc : Ploc.t) s =
  try
    (s |> Stream.of_string) |> Grammar.Entry.parse LLKGram.bootstrapped_top
  with Ploc.Exc (loc', exn) ->
    let rbt = Printexc.get_raw_backtrace () in
    let loc' =
      Ploc.
      (make_loc (file_name loc) (line_nb loc + line_nb loc') (bol_pos loc')
        (first_pos loc', last_pos loc') (comment loc'))
    in
    Printexc.raise_with_backtrace (Ploc.Exc (loc', exn)) rbt

  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
