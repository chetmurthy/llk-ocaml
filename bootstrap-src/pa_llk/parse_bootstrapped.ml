
open Pcaml

open Primtypes
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
          match
            assoc_matcher __strm__[@llk.first_follow "UIDENT \"LEFTA\" | UIDENT \"NONA\" | UIDENT \"RIGHTA\""]
          with
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
            [< '"", "GRAMMAR";
               e =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[e = grammar_body] expected after ['GRAMMAR'] (in [bootstrapped_top])"
                   grammar_body;
               '"", "END"; '"", ";"; '"EOI", _ >] ->
              norm_top e
        and bootstrapped_top_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "GRAMMAR") -> 0
          | _ -> raise Stream.Failure
        and e0 __strm__ =
          match
            e0_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\""]
          with
            0 ->
              (parser
                 [< '"", "(";
                    x =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x = e6] expected after ['('] (in [e0])" e6;
                    '"", ")" >] ->
                   x)
                __strm__
          | 1 ->
              (parser bp
                 [< '"", "["; '"", "^";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = LIST1 token] expected after ['['; '^'] (in [e0])"
                        (parse_list1 token);
                    '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   EXCEPT (loc, l))
                __strm__
          | 2 ->
              (parser bp
                 [< '"", "_" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in ANY loc)
                __strm__
          | 3 ->
              (parser bp
                 [< '"", "empty" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   DISJ (loc, []))
                __strm__
          | 4 ->
              (parser bp
                 [< '"", "eps" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in EPS loc)
                __strm__
          | 5 ->
              (parser bp
                 [< t = token >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   TOKEN (loc, t))
                __strm__
          | 6 ->
              (parser bp
                 [< '"LIDENT", x >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ID (loc, Name.mk x))
                __strm__
          | _ -> raise Stream.Failure
        and e0_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | Some ("", "[") -> 1
          | Some ("", "_") -> 2
          | Some ("", "empty") -> 3
          | Some ("", "eps") -> 4
          | Some ("STRING", _) -> 5
          | Some ("UIDENT", _) -> 5
          | Some ("", "#") -> 5
          | Some ("", "$") -> 5
          | Some ("LIDENT", _) -> 6
          | _ -> raise Stream.Failure
        and e1 =
          parser
            [< x = e0;
               a =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[x__0005 = e1__0013[<expr>]] expected after [x = e0] (in [e1])"
                   (e1__0013 x) >] ->
              a
        and e1_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | Some ("", "empty") -> 0
          | Some ("", "eps") -> 0
          | _ -> raise Stream.Failure
        and e1__0013 x __strm__ =
          match
            e1__0013_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"*\" | \"+\" | \"&\" | \";\" | \"?\" | \"in\" | \"|\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< '"", "*" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   STAR (loc, x))
                __strm__
          | 1 ->
              (parser bp
                 [< '"", "+" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   CONC (loc, [x; STAR (loc, x)]))
                __strm__
          | 2 -> (parser [< >] -> x) __strm__
          | _ -> raise Stream.Failure
        and e1__0013_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "*") -> 0
          | Some ("", "+") -> 1
          | Some ("LIDENT", _) -> 2
          | Some ("STRING", _) -> 2
          | Some ("UIDENT", _) -> 2
          | Some ("", "#") -> 2
          | Some ("", "$") -> 2
          | Some ("", "&") -> 2
          | Some ("", "(") -> 2
          | Some ("", ")") -> 2
          | Some ("", ";") -> 2
          | Some ("", "?") -> 2
          | Some ("", "[") -> 2
          | Some ("", "_") -> 2
          | Some ("", "empty") -> 2
          | Some ("", "eps") -> 2
          | Some ("", "in") -> 2
          | Some ("", "|") -> 2
          | Some ("", "~") -> 2
          | _ ->
              raise
                (Stream.Error
                   "['*'] or ['+'] or [<empty>] expected after [x = e0] (in [e1])")
        and e2 __strm__ =
          match
            e2_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< '"", "~";
                    x =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x = e2'] expected after ['~'] (in [e2])"
                        e2' >] ep ->
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
          | Some ("", "[") -> 1
          | Some ("", "_") -> 1
          | Some ("", "empty") -> 1
          | Some ("", "eps") -> 1
          | _ -> raise Stream.Failure
        and e2' =
          parser
            [< x = e1;
               a =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[x__0006 = e2'__0014[<expr>]] expected after [x = e1] (in [e2'])"
                   (e2'__0014 x) >] ->
              a
        and e2'_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | Some ("", "empty") -> 0
          | Some ("", "eps") -> 0
          | _ -> raise Stream.Failure
        and e2'__0014 x __strm__ =
          match
            e2'__0014_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"&\" | \";\" | \"?\" | \"in\" | \"|\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< '"", "?" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   OPT (loc, x))
                __strm__
          | 1 -> (parser [< >] -> x) __strm__
          | _ -> raise Stream.Failure
        and e2'__0014_matcher __strm__ =
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
          | Some ("", "[") -> 1
          | Some ("", "_") -> 1
          | Some ("", "empty") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | Some ("", "~") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['?'] or [<empty>] expected after [x = e1] (in [e2'])")
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
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | Some ("", "empty") -> 0
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
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | Some ("", "empty") -> 0
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
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | Some ("", "empty") -> 0
          | Some ("", "eps") -> 0
          | Some ("", "~") -> 0
          | _ -> raise Stream.Failure
        and e6 __strm__ =
          match
            e6_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\" | \"let\""]
          with
            0 ->
              (parser bp
                 [< '"", "let"; '"LIDENT", s; '"", "=";
                    re1 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[re1 = e5] expected after ['let'; s = LIDENT; '='] (in [e6])"
                        e5;
                    '"", "in";
                    re2 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[re2 = e6] expected after ['let'; s = LIDENT; '='; re1 = e5; 'in'] (in [e6])"
                        e6 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   LETIN (loc, Name.mk s, re1, re2))
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
          | Some ("", "[") -> 1
          | Some ("", "_") -> 1
          | Some ("", "empty") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "~") -> 1
          | _ -> raise Stream.Failure
        and entry =
          parser bp
            [< '"LIDENT", n;
               formals =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[formals = entry__0015] expected after [n = LIDENT] (in [entry])"
                   entry__0015;
               '"", ":";
               pos =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[pos = OPT position] expected after [n = LIDENT; formals = entry__0015; ':'] (in [entry])"
                   (parse_opt position);
               ll =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[ll = level_list] expected after [n = LIDENT; formals = entry__0015; ':'; pos = OPT position] (in [entry])"
                   level_list >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              {ae_loc = loc; ae_formals = formals; ae_name = Name.mk n;
               ae_pos = pos; ae_levels = ll; ae_preceding_psymbols = []}
        and entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and entry__0015 __strm__ =
          match
            entry__0015_matcher __strm__[@llk.first_follow "\"[\" | \":\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = LIST1 patt SEP ','] expected after [n = LIDENT; '['] (in [entry])"
                        (parse_list1_with_sep
                           (Grammar.Entry.parse_token_stream patt)
                           (parser [< '"", "," >] -> ()));
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and entry__0015_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("", ":") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['['] or [<empty>] expected after [n = LIDENT] (in [entry])")
        and exports =
          parser
            [< '"UIDENT", "EXPORT"; '"", ":";
               sl =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[sl = LIST1 LIDENT] expected after [UIDENT 'EXPORT'; ':'] (in [exports])"
                   (parse_list1 (parser [< '"LIDENT", __x__ >] -> __x__));
               '"", ";" >] ->
              List.map Name.mk sl
        and exports_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "EXPORT") -> 0
          | _ -> raise Stream.Failure
        and external_entry =
          parser
            [< '"", "external"; '"LIDENT", s; '"", ":";
               '"UIDENT", "PREDICTION";
               r =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[r = regexp] expected after ['external'; s = LIDENT; ':'; UIDENT 'PREDICTION'] (in [external_entry])"
                   regexp;
               '"", ";" >] ->
              Name.mk s, r
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
               extend_opt =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[extend_opt = OPT grammar_body__0016] expected after [gid = UIDENT; ':'] (in [grammar_body])"
                   (parse_opt grammar_body__0016);
               expl =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[expl = grammar_body__0017] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016] (in [grammar_body])"
                   grammar_body__0017;
               rl =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[rl = grammar_body__0018] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016; expl = grammar_body__0017] (in [grammar_body])"
                   grammar_body__0018;
               extl =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[extl = grammar_body__0019] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016; expl = grammar_body__0017; rl = grammar_body__0018] (in [grammar_body])"
                   grammar_body__0019;
               el =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[el = LIST1 grammar_body__0020] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016; expl = grammar_body__0017; rl = grammar_body__0018; extl = grammar_body__0019] (in [grammar_body])"
                   (parse_list1 grammar_body__0020) >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              {gram_loc = loc; gram_extend = extend_opt; gram_id = gid;
               gram_exports = expl; gram_external_asts = extl;
               gram_regexp_asts = rl; gram_entries = el}
        and grammar_body_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and grammar_body__0016 =
          parser
            [< '"", "EXTEND";
               id =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[id = longident_lident] expected after [gid = UIDENT; ':'; 'EXTEND'] (in [grammar_body])"
                   (Grammar.Entry.parse_token_stream longident_lident);
               '"", ";" >] ->
              id
        and grammar_body__0016_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "EXTEND") -> 0
          | _ ->
              raise
                (Stream.Error
                   "['EXTEND'] expected after [gid = UIDENT; ':'] (in [grammar_body])")
        and grammar_body__0017 __strm__ =
          match
            grammar_body__0017_matcher __strm__[@llk.first_follow "LIDENT | UIDENT \"EXPORT\" | \"external\" | UIDENT \"REGEXPS\""]
          with
            0 -> (parser [< a = exports >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0017_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "EXPORT") -> 0
          | Some ("UIDENT", "REGEXPS") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[l = exports] or [<empty>] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016] (in [grammar_body])")
        and grammar_body__0018 __strm__ =
          match
            grammar_body__0018_matcher __strm__[@llk.first_follow "LIDENT | \"external\" | UIDENT \"REGEXPS\""]
          with
            0 -> (parser [< a = regexps >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0018_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "REGEXPS") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[l = regexps] or [<empty>] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016; expl = grammar_body__0017] (in [grammar_body])")
        and grammar_body__0019 __strm__ =
          match
            grammar_body__0019_matcher __strm__[@llk.first_follow "LIDENT | \"external\""]
          with
            0 -> (parser [< a = externals >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0019_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | Some ("LIDENT", _) -> 1
          | _ ->
              raise
                (Stream.Error
                   "[l = externals] or [<empty>] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016; expl = grammar_body__0017; rl = grammar_body__0018] (in [grammar_body])")
        and grammar_body__0020 = parser [< e = entry; '"", ";" >] -> e
        and grammar_body__0020_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ ->
              raise
                (Stream.Error
                   "[e = entry] expected after [gid = UIDENT; ':'; extend_opt = OPT grammar_body__0016; expl = grammar_body__0017; rl = grammar_body__0018; extl = grammar_body__0019] (in [grammar_body])")
        and level =
          parser bp
            [< lab = parse_opt (parser [< '"STRING", __x__ >] -> __x__);
               ass =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[ass = OPT assoc] expected after [lab = OPT STRING] (in [level])"
                   (parse_opt assoc);
               rules =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[rules = rule_list] expected after [lab = OPT STRING; ass = OPT assoc] (in [level])"
                   rule_list >] ep ->
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
               ll =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[ll = LIST0 level SEP '|'] expected after ['['] (in [level_list])"
                   (parse_list0_with_sep level (parser [< '"", "|" >] -> ()));
               '"", "]" >] ->
              ll
        and level_list_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and paren_pattern =
          parser bp
            [< '"", "(";
               l =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[l = LIST1 pattern SEP ','] expected after ['('] (in [paren_pattern])"
                   (parse_list1_with_sep pattern
                      (parser [< '"", "," >] -> ()));
               '"", ")" >] ep ->
              let loc = Grammar.loc_of_token_interval bp ep in
              MLast.PaTup (loc, Ploc.VaVal l)
        and paren_pattern_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | _ -> raise Stream.Failure
        and pattern __strm__ =
          match
            pattern_matcher __strm__[@llk.first_follow "LIDENT | \"(\" | \"_\""]
          with
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
          match
            position_matcher __strm__[@llk.first_follow "UIDENT \"AFTER\" | UIDENT \"BEFORE\" | UIDENT \"FIRST\" | UIDENT \"LAST\" | UIDENT \"LEVEL\" | UIDENT \"LIKE\""]
          with
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
            psymbol_regexp __strm__[@llk.regexp "\"_\" #0 | LIDENT \"=\" #1 | LIDENT \"[\" #2 | \"(\" (LIDENT | \"(\" | \"_\" | \",\" | \")\")* \"=\" #3 | (LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"FLAG\" | UIDENT \"INFER\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\" | UIDENT \"V\") #4"]
          with
            Some (_, 0) ->
              (parser bp
                 [< '"", "_"; '"", "=";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol] expected after ['_'; '='] (in [psymbol])"
                        symbol >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc; ap_patt = Some (MLast.PaAny loc);
                    ap_symb = s})
                __strm__
          | Some (_, 1) ->
              (parser bp
                 [< '"LIDENT", p; '"", "=";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol] expected after [PREDICT check_lident_equal; p = LIDENT; '='] (in [psymbol])"
                        symbol >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc;
                    ap_patt = Some (MLast.PaLid (loc, Ploc.VaVal p));
                    ap_symb = s})
                __strm__
          | Some (_, 2) ->
              (parser bp
                 [< '"LIDENT", p;
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = psymbol__0021] expected after [PREDICT check_lident_lbracket; p = LIDENT] (in [psymbol])"
                        psymbol__0021;
                    lev =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[lev = OPT psymbol__0022] expected after [PREDICT check_lident_lbracket; p = LIDENT; args = psymbol__0021] (in [psymbol])"
                        (parse_opt psymbol__0022) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ap_loc = loc; ap_patt = None;
                    ap_symb = ASnterm (loc, Name.mk p, args, lev)})
                __strm__
          | Some (_, 3) ->
              (parser bp
                 [< p = paren_pattern; '"", "=";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol] expected after [PREDICT check_pattern_equal; p = paren_pattern; '='] (in [psymbol])"
                        symbol >] ep ->
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
            | Some ("UIDENT", "INFER") ->
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
        and psymbol__0021 __strm__ =
          match
            psymbol__0021_matcher __strm__[@llk.first_follow "\"[\" | \";\" | \"|\" | UIDENT \"LEVEL\" | \"->\" | \"]\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = LIST1 expr SEP ','] expected after [PREDICT check_lident_lbracket; p = LIDENT; '['] (in [psymbol])"
                        (parse_list1_with_sep
                           (Grammar.Entry.parse_token_stream expr)
                           (parser [< '"", "," >] -> ()));
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and psymbol__0021_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("UIDENT", "LEVEL") -> 1
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['['] or [<empty>] expected after [PREDICT check_lident_lbracket; p = LIDENT] (in [psymbol])")
        and psymbol__0022 = parser [< '"UIDENT", "LEVEL"; '"STRING", s >] -> s
        and psymbol__0022_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | _ ->
              raise
                (Stream.Error
                   "[UIDENT 'LEVEL'] expected after [PREDICT check_lident_lbracket; p = LIDENT; args = psymbol__0021] (in [psymbol])")
        and regexp = parser [< a = e6 >] -> a
        and regexp_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | Some ("", "empty") -> 0
          | Some ("", "eps") -> 0
          | Some ("", "let") -> 0
          | Some ("", "~") -> 0
          | _ -> raise Stream.Failure
        and regexp_entry =
          parser
            [< '"LIDENT", n; '"", "=";
               r =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[r = regexp] expected after [n = LIDENT; '='] (in [regexp_entry])"
                   regexp;
               '"", ";" >] ->
              Name.mk n, r
        and regexp_entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and regexps =
          parser
            [< '"UIDENT", "REGEXPS"; '"", ":";
               rl =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[rl = LIST1 regexp_entry] expected after [UIDENT 'REGEXPS'; ':'] (in [regexps])"
                   (parse_list1 regexp_entry);
               '"", "END"; '"", ";" >] ->
              rl
        and regexps_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "REGEXPS") -> 0
          | _ -> raise Stream.Failure
        and rule __strm__ =
          match
            rule_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | STRING | UIDENT \"FLAG\" | UIDENT \"INFER\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\""]
          with
            0 ->
              (parser bp
                 [< '"", "->";
                    act =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[act = expr] expected after ['->'] (in [rule])"
                        (Grammar.Entry.parse_token_stream expr) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ar_loc = loc; ar_psymbols = []; ar_action = Some act})
                __strm__
          | 1 ->
              (parser
                 [< psl =
                      parse_list1_with_sep psymbol
                        (parser [< '"", ";" >] -> ());
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0007 = rule__0023[<expr>]] expected after [psl = LIST1 psymbol SEP ';'] (in [rule])"
                        (rule__0023 psl) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and rule_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "->") -> 0
          | Some ("UIDENT", "FLAG") -> 1
          | Some ("UIDENT", "INFER") -> 1
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
        and rule__0023 psl __strm__ =
          match
            rule__0023_matcher __strm__[@llk.first_follow "\"|\" | \"->\" | \"]\""]
          with
            0 ->
              (parser bp
                 [< '"", "->";
                    act =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[act = expr] expected after [psl = LIST1 psymbol SEP ';'; '->'] (in [rule])"
                        (Grammar.Entry.parse_token_stream expr) >] ep ->
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
        and rule__0023_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "->") -> 0
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['->'] or [<empty>] expected after [psl = LIST1 psymbol SEP ';'] (in [rule])")
        and rule_list =
          parser
            [< '"", "[";
               a =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[x__0008 = rule_list__0024] expected after ['['] (in [rule_list])"
                   rule_list__0024 >] ->
              a
        and rule_list_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and rule_list__0024 __strm__ =
          match
            rule_list__0024_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | STRING | UIDENT \"FLAG\" | UIDENT \"INFER\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\" | \"]\""]
          with
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
        and rule_list__0024_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "]") -> 0
          | Some ("UIDENT", "FLAG") -> 1
          | Some ("UIDENT", "INFER") -> 1
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
          | _ ->
              raise
                (Stream.Error
                   "[']'] or [rules = LIST1 rule SEP '|'] expected after ['['] (in [rule_list])")
        and sep_opt_sep =
          parser
            [< '"UIDENT", ("SEP" as sep);
               t =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[t = symbol] expected after [sep = UIDENT 'SEP'] (in [sep_opt_sep])"
                   symbol;
               b =
                 Pa_llk_runtime.Llk_runtime.must_parse
                   ~msg:"[b = FLAG sep_opt_sep__0025] expected after [sep = UIDENT 'SEP'; t = symbol] (in [sep_opt_sep])"
                   (parse_flag sep_opt_sep__0025) >] ->
              t, b
        and sep_opt_sep_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "SEP") -> 0
          | _ -> raise Stream.Failure
        and sep_opt_sep__0025 = parser [< '"UIDENT", "OPT_SEP" >] -> ()
        and sep_opt_sep__0025_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "OPT_SEP") -> 0
          | _ ->
              raise
                (Stream.Error
                   "[UIDENT 'OPT_SEP'] expected after [sep = UIDENT 'SEP'; t = symbol] (in [sep_opt_sep])")
        and symbol = parser [< a = symbol__0001 >] -> a
        and symbol_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "INFER") -> 0
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
          match
            symbol__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"FLAG\" | UIDENT \"INFER\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\" | UIDENT \"V\""]
          with
            0 ->
              (parser bp
                 [< '"UIDENT", "FLAG";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0002] expected after [UIDENT 'FLAG'] (in [symbol])"
                        symbol__0002 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASflag (loc, s))
                __strm__
          | 1 ->
              (parser bp
                 [< '"UIDENT", "LEFT_ASSOC";
                    s1 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s1 = symbol__0002] expected after [UIDENT 'LEFT_ASSOC'] (in [symbol])"
                        symbol__0002;
                    '"UIDENT", "ACCUMULATE";
                    s2 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s2 = symbol__0002] expected after [UIDENT 'LEFT_ASSOC'; s1 = symbol__0002; UIDENT 'ACCUMULATE'] (in [symbol])"
                        symbol__0002;
                    '"UIDENT", "WITH";
                    e =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[e = expr_LEVEL_simple] expected after [UIDENT 'LEFT_ASSOC'; s1 = symbol__0002; UIDENT 'ACCUMULATE'; s2 = symbol__0002; UIDENT 'WITH'] (in [symbol])"
                        (Grammar.Entry.parse_token_stream
                           expr_LEVEL_simple) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASleft_assoc (loc, s1, s2, e))
                __strm__
          | 2 ->
              (parser bp
                 [< '"UIDENT", "LIST0";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0002] expected after [UIDENT 'LIST0'] (in [symbol])"
                        symbol__0002;
                    sep =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[sep = OPT sep_opt_sep] expected after [UIDENT 'LIST0'; s = symbol__0002] (in [symbol])"
                        (parse_opt sep_opt_sep) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASlist (loc, LML_0, s, sep))
                __strm__
          | 3 ->
              (parser bp
                 [< '"UIDENT", "LIST1";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0002] expected after [UIDENT 'LIST1'] (in [symbol])"
                        symbol__0002;
                    sep =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[sep = OPT sep_opt_sep] expected after [UIDENT 'LIST1'; s = symbol__0002] (in [symbol])"
                        (parse_opt sep_opt_sep) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASlist (loc, LML_1, s, sep))
                __strm__
          | 4 ->
              (parser bp
                 [< '"UIDENT", "OPT";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0002] expected after [UIDENT 'OPT'] (in [symbol])"
                        symbol__0002 >] ep ->
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
          | Some ("UIDENT", "INFER") -> 5
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
          match
            symbol__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"INFER\" | UIDENT \"NEXT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\" | UIDENT \"V\""]
          with
            0 ->
              (parser bp
                 [< '"UIDENT", "V";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0002] expected after [UIDENT 'V'] (in [symbol])"
                        symbol__0002;
                    al =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[al = LIST0 STRING] expected after [UIDENT 'V'; s = symbol__0002] (in [symbol])"
                        (parse_list0
                           (parser [< '"STRING", __x__ >] -> __x__)) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASvala (loc, s, al))
                __strm__
          | 1 -> (parser [< a = symbol__0003 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "V") -> 0
          | Some ("UIDENT", "INFER") -> 1
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
          match
            symbol__0003_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"INFER\" | UIDENT \"NEXT\" | UIDENT \"PREDICT\" | UIDENT \"SELF\""]
          with
            0 ->
              (parser
                 [< '"", "(";
                    s_t =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s_t = symbol__0001] expected after ['('] (in [symbol])"
                        symbol__0001;
                    '"", ")";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0009 = symbol__0026[<expr>]] expected after ['('; s_t = symbol__0001; ')'] (in [symbol])"
                        (symbol__0026 s_t) >] ->
                   a)
                __strm__
          | 1 ->
              (parser bp
                 [< '"", "[";
                    rl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[rl = LIST0 rule SEP '|'] expected after ['['] (in [symbol])"
                        (parse_list0_with_sep rule
                           (parser [< '"", "|" >] -> ()));
                    '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASrules (loc, {au_loc = loc; au_rules = rl}))
                __strm__
          | 2 ->
              (parser bp
                 [< '"UIDENT", "INFER"; '"INT", n >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASinfer (loc, int_of_string n))
                __strm__
          | 3 ->
              (parser bp
                 [< '"UIDENT", "NEXT";
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = symbol__0027] expected after [UIDENT 'NEXT'] (in [symbol])"
                        symbol__0027 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASnext (loc, args))
                __strm__
          | 4 ->
              (parser bp
                 [< '"UIDENT", "PREDICT"; '"LIDENT", id >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASregexp (loc, Name.mk id))
                __strm__
          | 5 ->
              (parser bp
                 [< '"UIDENT", "SELF";
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = symbol__0028] expected after [UIDENT 'SELF'] (in [symbol])"
                        symbol__0028 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASself (loc, args))
                __strm__
          | 6 ->
              (parser bp
                 [< '"STRING", e >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASkeyw (loc, e))
                __strm__
          | 7 ->
              (parser bp
                 [< '"LIDENT", id;
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = symbol__0029] expected after [id = LIDENT] (in [symbol])"
                        symbol__0029;
                    lev =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[lev = OPT symbol__0030] expected after [id = LIDENT; args = symbol__0029] (in [symbol])"
                        (parse_opt symbol__0030) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASnterm (loc, Name.mk id, args, lev))
                __strm__
          | 8 ->
              (parser
                 [< '"UIDENT", x;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0010 = symbol__0031[<expr>]] expected after [x = UIDENT] (in [symbol])"
                        (symbol__0031 x) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | Some ("", "[") -> 1
          | Some ("UIDENT", "INFER") -> 2
          | Some ("UIDENT", "NEXT") -> 3
          | Some ("UIDENT", "PREDICT") -> 4
          | Some ("UIDENT", "SELF") -> 5
          | Some ("STRING", _) -> 6
          | Some ("LIDENT", _) -> 7
          | Some ("UIDENT", _) -> 8
          | _ -> raise Stream.Failure
        and symbol__0026 s_t __strm__ =
          match
            symbol__0026_matcher __strm__[@llk.first_follow "\")\" | STRING | \";\" | \"?\" | \"|\" | \"->\" | \"]\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser bp
                 [< '"", "?" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASsyntactic (loc, s_t))
                __strm__
          | 1 -> (parser [< >] -> s_t) __strm__
          | _ -> raise Stream.Failure
        and symbol__0026_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "?") -> 0
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
          | _ ->
              raise
                (Stream.Error
                   "['?'] or [<empty>] expected after ['('; s_t = symbol__0001; ')'] (in [symbol])")
        and symbol__0027 __strm__ =
          match
            symbol__0027_matcher __strm__[@llk.first_follow "\"[\" | \")\" | STRING | \";\" | \"|\" | \"->\" | \"]\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = LIST1 expr SEP ','] expected after [UIDENT 'NEXT'; '['] (in [symbol])"
                        (parse_list1_with_sep
                           (Grammar.Entry.parse_token_stream expr)
                           (parser [< '"", "," >] -> ()));
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0027_matcher __strm__ =
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
          | _ ->
              raise
                (Stream.Error
                   "['['] or [<empty>] expected after [UIDENT 'NEXT'] (in [symbol])")
        and symbol__0028 __strm__ =
          match
            symbol__0028_matcher __strm__[@llk.first_follow "\"[\" | \")\" | STRING | \";\" | \"|\" | \"->\" | \"]\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = LIST1 expr SEP ','] expected after [UIDENT 'SELF'; '['] (in [symbol])"
                        (parse_list1_with_sep
                           (Grammar.Entry.parse_token_stream expr)
                           (parser [< '"", "," >] -> ()));
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0028_matcher __strm__ =
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
          | _ ->
              raise
                (Stream.Error
                   "['['] or [<empty>] expected after [UIDENT 'SELF'] (in [symbol])")
        and symbol__0029 __strm__ =
          match
            symbol__0029_matcher __strm__[@llk.first_follow "\"[\" | \")\" | STRING | \";\" | \"|\" | UIDENT \"LEVEL\" | \"->\" | \"]\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = LIST1 expr SEP ','] expected after [id = LIDENT; '['] (in [symbol])"
                        (parse_list1_with_sep
                           (Grammar.Entry.parse_token_stream expr)
                           (parser [< '"", "," >] -> ()));
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0029_matcher __strm__ =
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
          | _ ->
              raise
                (Stream.Error
                   "['['] or [<empty>] expected after [id = LIDENT] (in [symbol])")
        and symbol__0030 = parser [< '"UIDENT", "LEVEL"; '"STRING", s >] -> s
        and symbol__0030_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | _ ->
              raise
                (Stream.Error
                   "[UIDENT 'LEVEL'] expected after [id = LIDENT; args = symbol__0029] (in [symbol])")
        and symbol__0031 x __strm__ =
          match
            symbol__0031_matcher __strm__[@llk.first_follow "\")\" | STRING | \";\" | \"|\" | \"->\" | \"]\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\" | \"/\""]
          with
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
        and symbol__0031_matcher __strm__ =
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
          | _ ->
              raise
                (Stream.Error
                   "['/'] or [<empty>] expected after [x = UIDENT] (in [symbol])")
        and token __strm__ =
          match
            token_matcher __strm__[@llk.first_follow "UIDENT | STRING | \"#\" | \"$\""]
          with
            0 ->
              (parser [< '"", "#"; '"INT", x >] -> Output (int_of_string x))
                __strm__
          | 1 ->
              (parser
                 [< '"", "$";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0011 = token__0032] expected after ['$'] (in [token])"
                        token__0032 >] ->
                   a)
                __strm__
          | 2 -> (parser [< '"STRING", x >] -> Special x) __strm__
          | 3 ->
              (parser
                 [< '"UIDENT", x;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0012 = token__0033[<expr>]] expected after [x = UIDENT] (in [token])"
                        (token__0033 x) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and token_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "#") -> 0
          | Some ("", "$") -> 1
          | Some ("STRING", _) -> 2
          | Some ("UIDENT", _) -> 3
          | _ -> raise Stream.Failure
        and token__0032 __strm__ =
          match
            token__0032_matcher __strm__[@llk.first_follow "LIDENT | STRING"]
          with
            0 -> (parser [< '"LIDENT", x >] -> Anti x) __strm__
          | 1 ->
              (parser [< '"STRING", x >] -> Anti (Scanf.unescaped x)) __strm__
          | _ -> raise Stream.Failure
        and token__0032_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 1
          | _ ->
              raise
                (Stream.Error
                   "[x = LIDENT] or [x = STRING] expected after ['$'] (in [token])")
        and token__0033 x __strm__ =
          match
            token__0033_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"*\" | \"+\" | \"&\" | \";\" | \"?\" | \"in\" | \"|\" | \"~\" | \"]\" | \"/\""]
          with
            0 ->
              (parser [< '"", "/"; '"STRING", s >] -> Class (x, Some s))
                __strm__
          | 1 -> (parser [< >] -> Class (x, None)) __strm__
          | _ -> raise Stream.Failure
        and token__0033_matcher __strm__ =
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
          | Some ("", "+") -> 1
          | Some ("", ";") -> 1
          | Some ("", "?") -> 1
          | Some ("", "[") -> 1
          | Some ("", "]") -> 1
          | Some ("", "_") -> 1
          | Some ("", "empty") -> 1
          | Some ("", "eps") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | Some ("", "~") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['/'] or [<empty>] expected after [x = UIDENT] (in [token])")
      end
    module Top =
      struct
        let bootstrapped_top __strm__ =
          try F.bootstrapped_top __strm__ with
            Stream.Failure ->
              raise (Stream.Error "illegal begin of bootstrapped_top")
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
      lexer.tok_using ("UIDENT", "");
      lexer.tok_using ("", "#");
      lexer.tok_using ("", "$");
      lexer.tok_using ("", "&");
      lexer.tok_using ("", "(");
      lexer.tok_using ("", ")");
      lexer.tok_using ("", "*");
      lexer.tok_using ("", "+");
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
      lexer.tok_using ("", "^");
      lexer.tok_using ("", "_");
      lexer.tok_using ("", "empty");
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

let pa loc s =
  let g =
    (s |> Stream.of_string) |> Grammar.Entry.parse LLKGram.bootstrapped_top
  in
  {g with gram_loc = loc}
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
