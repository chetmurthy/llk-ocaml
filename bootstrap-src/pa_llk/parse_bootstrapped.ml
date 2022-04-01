
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
            assoc_matcher __strm__[@llk.first_follow "UIDENT \"NONA\" | UIDENT \"RIGHTA\" | UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\""]
          with
            0 -> (parser [< '"UIDENT", "NONA" >] -> NONA) __strm__
          | 1 -> (parser [< '"UIDENT", "RIGHTA" >] -> RIGHTA) __strm__
          | 2 ->
              (parser [< g = assoc__0001; '"UIDENT", "LEFTA" >] -> LEFTA g)
                __strm__
          | _ -> raise Stream.Failure
        and assoc_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "NONA") -> 0
          | Some ("UIDENT", "RIGHTA") -> 1
          | Some ("UIDENT", "GREEDY") -> 2
          | Some ("UIDENT", "LEFTA") -> 2
          | Some ("UIDENT", "NONGREEDY") -> 2
          | _ -> raise Stream.Failure
        and assoc__0001 __strm__ =
          match
            assoc__0001_matcher __strm__[@llk.first_follow "UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\""]
          with
            0 -> (parser [< '"UIDENT", "GREEDY" >] -> true) __strm__
          | 1 -> (parser [< '"UIDENT", "NONGREEDY" >] -> false) __strm__
          | 2 -> (parser [< >] -> true) __strm__
          | _ -> raise Stream.Failure
        and assoc__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 1
          | Some ("UIDENT", "LEFTA") -> 2
          | _ -> raise Stream.Failure
        and bootstrapped_top __strm__ =
          match
            bootstrapped_top_matcher __strm__[@llk.first_follow "\"GRAMMAR\""]
          with
            0 ->
              (parser
                 [< '"", "GRAMMAR";
                    e =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[e = grammar_body] expected after ['GRAMMAR'] (in [bootstrapped_top])"
                        grammar_body;
                    '"", "END"; '"", ";"; '"EOI", _ >] ->
                   norm_top e)
                __strm__
          | _ -> raise Stream.Failure
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
                        ~msg:"[l = e0__0001] expected after ['['; '^'] (in [e0])"
                        e0__0001;
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
        and e0__0001 __strm__ =
          match
            e0__0001_matcher __strm__[@llk.first_follow "UIDENT | STRING | \"#\" | \"$\""]
          with
            0 ->
              (parser
                 [< x__0010 = token;
                    y__0001 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0001 = e0__0002] expected after [x__0010 = token] (in [e0])"
                        e0__0002 >] ->
                   x__0010 :: y__0001)
                __strm__
          | _ -> raise Stream.Failure
        and e0__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | _ -> raise Stream.Failure
        and e0__0002 __strm__ =
          match
            e0__0002_matcher __strm__[@llk.first_follow "UIDENT | STRING | \"#\" | \"$\" | \"]\""]
          with
            0 ->
              (parser
                 [< x__0011 = token;
                    y__0002 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0002 = e0__0002] expected after [x__0011 = token] (in [e0])"
                        e0__0002 >] ->
                   x__0011 :: y__0002)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and e0__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "#") -> 0
          | Some ("", "$") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and e1 __strm__ =
          match
            e1_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\""]
          with
            0 ->
              (parser
                 [< x = e0;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0001 = e1__0001[<expr>]] expected after [x = e0] (in [e1])"
                        (e1__0001 x) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
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
        and e1__0001 x __strm__ =
          match
            e1__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"*\" | \"+\" | \"&\" | \";\" | \"?\" | \"in\" | \"|\" | \"~\""]
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
        and e1__0001_matcher __strm__ =
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
        and e2' __strm__ =
          match
            e2'_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\""]
          with
            0 ->
              (parser
                 [< x = e1;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0002 = e2'__0001[<expr>]] expected after [x = e1] (in [e2'])"
                        (e2'__0001 x) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
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
        and e2'__0001 x __strm__ =
          match
            e2'__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"&\" | \";\" | \"?\" | \"in\" | \"|\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< '"", "?" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   OPT (loc, x))
                __strm__
          | 1 -> (parser [< >] -> x) __strm__
          | _ -> raise Stream.Failure
        and e2'__0001_matcher __strm__ =
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
        and e3 __strm__ =
          match
            e3_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< l = e3__0001 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   CONC (loc, l))
                __strm__
          | _ -> raise Stream.Failure
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
        and e3__0001 __strm__ =
          match
            e3__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser
                 [< x__0012 = e2;
                    y__0003 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0003 = e3__0002] expected after [x__0012 = e2] (in [e3])"
                        e3__0002 >] ->
                   x__0012 :: y__0003)
                __strm__
          | _ -> raise Stream.Failure
        and e3__0001_matcher __strm__ =
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
        and e3__0002 __strm__ =
          match
            e3__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"&\" | \";\" | \"in\" | \"|\" | \"~\""]
          with
            0 ->
              (parser
                 [< x__0013 = e2;
                    y__0004 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0004 = e3__0002] expected after [x__0013 = e2] (in [e3])"
                        e3__0002 >] ->
                   x__0013 :: y__0004)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and e3__0002_matcher __strm__ =
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
          | Some ("", "&") -> 1
          | Some ("", ")") -> 1
          | Some ("", ";") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and e4 __strm__ =
          match
            e4_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< l = e4__0001 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   CONJ (loc, l))
                __strm__
          | _ -> raise Stream.Failure
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
        and e4__0001 __strm__ =
          match
            e4__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser
                 [< x__0014 = e3;
                    y__0005 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0005 = e4__0002] expected after [x__0014 = e3] (in [e4])"
                        e4__0002 >] ->
                   x__0014 :: y__0005)
                __strm__
          | _ -> raise Stream.Failure
        and e4__0001_matcher __strm__ =
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
        and e4__0002 __strm__ =
          match
            e4__0002_matcher __strm__[@llk.first_follow "\")\" | \"&\" | \";\" | \"in\" | \"|\""]
          with
            0 ->
              (parser
                 [< x__0015 = e4__0003;
                    y__0006 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0006 = e4__0002] expected after [x__0015 = e4__0003] (in [e4])"
                        e4__0002 >] ->
                   x__0015 :: y__0006)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and e4__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "&") -> 0
          | Some ("", ")") -> 1
          | Some ("", ";") -> 1
          | Some ("", "in") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and e4__0003 __strm__ =
          match e4__0003_matcher __strm__[@llk.first_follow "\"&\""] with
            0 ->
              (parser
                 [< '"", "&";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0005 = e3] expected after ['&'] (in [e4])"
                        e3 >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and e4__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "&") -> 0
          | _ -> raise Stream.Failure
        and e5 __strm__ =
          match
            e5_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser bp
                 [< l = e5__0001 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   DISJ (loc, l))
                __strm__
          | _ -> raise Stream.Failure
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
        and e5__0001 __strm__ =
          match
            e5__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\""]
          with
            0 ->
              (parser
                 [< x__0016 = e4;
                    y__0007 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0007 = e5__0002] expected after [x__0016 = e4] (in [e5])"
                        e5__0002 >] ->
                   x__0016 :: y__0007)
                __strm__
          | _ -> raise Stream.Failure
        and e5__0001_matcher __strm__ =
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
        and e5__0002 __strm__ =
          match
            e5__0002_matcher __strm__[@llk.first_follow "\")\" | \";\" | \"in\" | \"|\""]
          with
            0 ->
              (parser
                 [< x__0017 = e5__0003;
                    y__0008 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0008 = e5__0002] expected after [x__0017 = e5__0003] (in [e5])"
                        e5__0002 >] ->
                   x__0017 :: y__0008)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and e5__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | Some ("", ")") -> 1
          | Some ("", ";") -> 1
          | Some ("", "in") -> 1
          | _ -> raise Stream.Failure
        and e5__0003 __strm__ =
          match e5__0003_matcher __strm__[@llk.first_follow "\"|\""] with
            0 ->
              (parser
                 [< '"", "|";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0007 = e4] expected after ['|'] (in [e5])"
                        e4 >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and e5__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
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
        and entry __strm__ =
          match entry_matcher __strm__[@llk.first_follow "LIDENT"] with
            0 ->
              (parser bp
                 [< '"LIDENT", n;
                    formals =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[formals = entry__0001] expected after [n = LIDENT] (in [entry])"
                        entry__0001;
                    '"", ":";
                    pos =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[pos = entry__0004] expected after [n = LIDENT; formals = entry__0001; ':'] (in [entry])"
                        entry__0004;
                    ll =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[ll = level_list] expected after [n = LIDENT; formals = entry__0001; ':'; pos = entry__0004] (in [entry])"
                        level_list >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {ae_loc = loc; ae_formals = formals; ae_name = Name.mk n;
                    ae_pos = pos; ae_levels = ll; ae_preceding_psymbols = [];
                    ae_source_symbol = None})
                __strm__
          | _ -> raise Stream.Failure
        and entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and entry__0001 __strm__ =
          match
            entry__0001_matcher __strm__[@llk.first_follow "\"[\" | \":\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = entry__0002] expected after [n = LIDENT; '['] (in [entry])"
                        entry__0002;
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and entry__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | Some ("", ":") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['['] or [<empty>] expected after [n = LIDENT] (in [entry])")
        and entry__0002 __strm__ =
          match
            entry__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | INT | QUOTATION | \"{\""]
          with
            0 ->
              (parser
                 [< x__0018 = Grammar.Entry.parse_token_stream patt;
                    y__0009 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0009 = entry__0003] expected after [x__0018 = patt] (in [entry])"
                        entry__0003 >] ->
                   x__0018 :: y__0009)
                __strm__
          | _ -> raise Stream.Failure
        and entry__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("INT", _) -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("QUOTATION", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "{") -> 0
          | _ -> raise Stream.Failure
        and entry__0003 __strm__ =
          match
            entry__0003_matcher __strm__[@llk.first_follow "\",\" | \"]\""]
          with
            0 ->
              (parser
                 [< x__0019 = entry__0005;
                    y__0010 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0010 = entry__0003] expected after [x__0019 = entry__0005] (in [entry])"
                        entry__0003 >] ->
                   x__0019 :: y__0010)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and entry__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and entry__0004 __strm__ =
          match
            entry__0004_matcher __strm__[@llk.first_follow "\"[\" | UIDENT \"AFTER\" | UIDENT \"BEFORE\" | UIDENT \"FIRST\" | UIDENT \"LAST\" | UIDENT \"LEVEL\" | UIDENT \"LIKE\""]
          with
            0 -> (parser [< x__0051 = position >] -> Some x__0051) __strm__
          | 1 -> (parser [< >] -> None) __strm__
          | _ -> raise Stream.Failure
        and entry__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "AFTER") -> 0
          | Some ("UIDENT", "BEFORE") -> 0
          | Some ("UIDENT", "FIRST") -> 0
          | Some ("UIDENT", "LAST") -> 0
          | Some ("UIDENT", "LEVEL") -> 0
          | Some ("UIDENT", "LIKE") -> 0
          | Some ("", "[") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[x__0051 = position] or [<empty>] expected after [n = LIDENT; formals = entry__0001; ':'] (in [entry])")
        and entry__0005 __strm__ =
          match entry__0005_matcher __strm__[@llk.first_follow "\",\""] with
            0 ->
              (parser
                 [< '"", ",";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0009 = patt] expected after [','] (in [entry])"
                        (Grammar.Entry.parse_token_stream patt) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and entry__0005_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | _ -> raise Stream.Failure
        and exports __strm__ =
          match
            exports_matcher __strm__[@llk.first_follow "UIDENT \"EXPORT\""]
          with
            0 ->
              (parser
                 [< '"UIDENT", "EXPORT"; '"", ":";
                    sl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[sl = exports__0001] expected after [UIDENT 'EXPORT'; ':'] (in [exports])"
                        exports__0001;
                    '"", ";" >] ->
                   List.map Name.mk sl)
                __strm__
          | _ -> raise Stream.Failure
        and exports_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "EXPORT") -> 0
          | _ -> raise Stream.Failure
        and exports__0001 __strm__ =
          match
            exports__0001_matcher __strm__[@llk.first_follow "LIDENT"]
          with
            0 ->
              (parser
                 [< '"LIDENT", x__0020;
                    y__0011 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0011 = exports__0002] expected after [x__0020 = LIDENT] (in [exports])"
                        exports__0002 >] ->
                   x__0020 :: y__0011)
                __strm__
          | _ -> raise Stream.Failure
        and exports__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and exports__0002 __strm__ =
          match
            exports__0002_matcher __strm__[@llk.first_follow "LIDENT | \";\""]
          with
            0 ->
              (parser
                 [< '"LIDENT", x__0021;
                    y__0012 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0012 = exports__0002] expected after [x__0021 = LIDENT] (in [exports])"
                        exports__0002 >] ->
                   x__0021 :: y__0012)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and exports__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("", ";") -> 1
          | _ -> raise Stream.Failure
        and external_entry __strm__ =
          match
            external_entry_matcher __strm__[@llk.first_follow "\"external\""]
          with
            0 ->
              (parser
                 [< '"", "external"; '"LIDENT", s; '"", ":";
                    '"UIDENT", "PREDICTION";
                    r =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[r = regexp] expected after ['external'; s = LIDENT; ':'; UIDENT 'PREDICTION'] (in [external_entry])"
                        regexp;
                    '"", ";" >] ->
                   Name.mk s, r)
                __strm__
          | _ -> raise Stream.Failure
        and external_entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | _ -> raise Stream.Failure
        and externals __strm__ =
          match
            externals_matcher __strm__[@llk.first_follow "\"external\""]
          with
            0 -> (parser [< a = externals__0001 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and externals_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | _ -> raise Stream.Failure
        and externals__0001 __strm__ =
          match
            externals__0001_matcher __strm__[@llk.first_follow "\"external\""]
          with
            0 ->
              (parser
                 [< x__0022 = external_entry;
                    y__0013 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0013 = externals__0002] expected after [x__0022 = external_entry] (in [externals])"
                        externals__0002 >] ->
                   x__0022 :: y__0013)
                __strm__
          | _ -> raise Stream.Failure
        and externals__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | _ -> raise Stream.Failure
        and externals__0002 __strm__ =
          match
            externals__0002_matcher __strm__[@llk.first_follow "LIDENT | \"external\""]
          with
            0 ->
              (parser
                 [< x__0023 = external_entry;
                    y__0014 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0014 = externals__0002] expected after [x__0023 = external_entry] (in [externals])"
                        externals__0002 >] ->
                   x__0023 :: y__0014)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and externals__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | Some ("LIDENT", _) -> 1
          | _ -> raise Stream.Failure
        and grammar_body __strm__ =
          match grammar_body_matcher __strm__[@llk.first_follow "UIDENT"] with
            0 ->
              (parser bp
                 [< '"UIDENT", gid; '"", ":";
                    extend_opt =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[extend_opt = grammar_body__0008] expected after [gid = UIDENT; ':'] (in [grammar_body])"
                        grammar_body__0008;
                    expl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[expl = grammar_body__0002] expected after [gid = UIDENT; ':'; extend_opt = grammar_body__0008] (in [grammar_body])"
                        grammar_body__0002;
                    rl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[rl = grammar_body__0003] expected after [gid = UIDENT; ':'; extend_opt = grammar_body__0008; expl = grammar_body__0002] (in [grammar_body])"
                        grammar_body__0003;
                    extl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[extl = grammar_body__0004] expected after [gid = UIDENT; ':'; extend_opt = grammar_body__0008; expl = grammar_body__0002; rl = grammar_body__0003] (in [grammar_body])"
                        grammar_body__0004;
                    el =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[el = grammar_body__0006] expected after [gid = UIDENT; ':'; extend_opt = grammar_body__0008; expl = grammar_body__0002; rl = grammar_body__0003; extl = grammar_body__0004] (in [grammar_body])"
                        grammar_body__0006 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {gram_loc = loc; gram_extend = extend_opt; gram_id = gid;
                    gram_exports = expl; gram_external_asts = extl;
                    gram_regexp_asts = rl; gram_entries = el})
                __strm__
          | _ -> raise Stream.Failure
        and grammar_body_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and grammar_body__0001 __strm__ =
          match
            grammar_body__0001_matcher __strm__[@llk.first_follow "\"EXTEND\""]
          with
            0 ->
              (parser
                 [< '"", "EXTEND";
                    id =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[id = longident_lident] expected after ['EXTEND'] (in [grammar_body])"
                        (Grammar.Entry.parse_token_stream longident_lident);
                    '"", ";" >] ->
                   id)
                __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "EXTEND") -> 0
          | _ -> raise Stream.Failure
        and grammar_body__0002 __strm__ =
          match
            grammar_body__0002_matcher __strm__[@llk.first_follow "LIDENT | UIDENT \"EXPORT\" | \"external\" | UIDENT \"REGEXPS\""]
          with
            0 -> (parser [< a = exports >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "EXPORT") -> 0
          | Some ("UIDENT", "REGEXPS") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[l = exports] or [<empty>] expected after [gid = UIDENT; ':'; extend_opt = [ x__0053 = grammar_body__0001 \226\134\146 <expr> | \226\134\146 <expr> ]] (in [grammar_body])")
        and grammar_body__0003 __strm__ =
          match
            grammar_body__0003_matcher __strm__[@llk.first_follow "LIDENT | \"external\" | UIDENT \"REGEXPS\""]
          with
            0 -> (parser [< a = regexps >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "REGEXPS") -> 0
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[l = regexps] or [<empty>] expected after [gid = UIDENT; ':'; extend_opt = [ x__0054 = grammar_body__0001 \226\134\146 <expr> | \226\134\146 <expr> ]; expl = grammar_body__0002] (in [grammar_body])")
        and grammar_body__0004 __strm__ =
          match
            grammar_body__0004_matcher __strm__[@llk.first_follow "LIDENT | \"external\""]
          with
            0 -> (parser [< a = externals >] -> a) __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "external") -> 0
          | Some ("LIDENT", _) -> 1
          | _ ->
              raise
                (Stream.Error
                   "[l = externals] or [<empty>] expected after [gid = UIDENT; ':'; extend_opt = [ x__0055 = grammar_body__0001 \226\134\146 <expr> | \226\134\146 <expr> ]; expl = grammar_body__0002; rl = grammar_body__0003] (in [grammar_body])")
        and grammar_body__0005 __strm__ =
          match
            grammar_body__0005_matcher __strm__[@llk.first_follow "LIDENT"]
          with
            0 -> (parser [< e = entry; '"", ";" >] -> e) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0005_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and grammar_body__0006 __strm__ =
          match
            grammar_body__0006_matcher __strm__[@llk.first_follow "LIDENT"]
          with
            0 ->
              (parser
                 [< x__0024 = grammar_body__0005;
                    y__0015 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0015 = grammar_body__0007] expected after [x__0024 = grammar_body__0005] (in [grammar_body])"
                        grammar_body__0007 >] ->
                   x__0024 :: y__0015)
                __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0006_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and grammar_body__0007 __strm__ =
          match
            grammar_body__0007_matcher __strm__[@llk.first_follow "LIDENT | \"END\""]
          with
            0 ->
              (parser
                 [< x__0025 = grammar_body__0005;
                    y__0016 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0016 = grammar_body__0007] expected after [x__0025 = grammar_body__0005] (in [grammar_body])"
                        grammar_body__0007 >] ->
                   x__0025 :: y__0016)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0007_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("", "END") -> 1
          | _ -> raise Stream.Failure
        and grammar_body__0008 __strm__ =
          match
            grammar_body__0008_matcher __strm__[@llk.first_follow "LIDENT | UIDENT \"EXPORT\" | \"external\" | \"EXTEND\" | UIDENT \"REGEXPS\""]
          with
            0 ->
              (parser [< x__0052 = grammar_body__0001 >] -> Some x__0052)
                __strm__
          | 1 -> (parser [< >] -> None) __strm__
          | _ -> raise Stream.Failure
        and grammar_body__0008_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "EXTEND") -> 0
          | Some ("UIDENT", "EXPORT") -> 1
          | Some ("UIDENT", "REGEXPS") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("", "external") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[x__0052 = grammar_body__0001] or [<empty>] expected after [gid = UIDENT; ':'] (in [grammar_body])")
        and level __strm__ =
          match
            level_matcher __strm__[@llk.first_follow "\"[\" | UIDENT \"NONA\" | UIDENT \"RIGHTA\" | UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\" | STRING"]
          with
            0 ->
              (parser bp
                 [< lab = level__0001;
                    ass =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[ass = level__0002] expected after [lab = level__0001] (in [level])"
                        level__0002;
                    rules =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[rules = rule_list] expected after [lab = level__0001; ass = level__0002] (in [level])"
                        rule_list >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {al_loc = loc; al_label = lab; al_assoc = ass;
                    al_rules = rules})
                __strm__
          | _ -> raise Stream.Failure
        and level_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFTA") -> 0
          | Some ("UIDENT", "NONA") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "RIGHTA") -> 0
          | Some ("STRING", _) -> 0
          | Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and level__0001 __strm__ =
          match
            level__0001_matcher __strm__[@llk.first_follow "\"[\" | UIDENT \"NONA\" | UIDENT \"RIGHTA\" | UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\" | STRING"]
          with
            0 -> (parser [< '"STRING", x__0056 >] -> Some x__0056) __strm__
          | 1 -> (parser [< >] -> None) __strm__
          | _ -> raise Stream.Failure
        and level__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("STRING", _) -> 0
          | Some ("UIDENT", "GREEDY") -> 1
          | Some ("UIDENT", "LEFTA") -> 1
          | Some ("UIDENT", "NONA") -> 1
          | Some ("UIDENT", "NONGREEDY") -> 1
          | Some ("UIDENT", "RIGHTA") -> 1
          | Some ("", "[") -> 1
          | _ -> raise Stream.Failure
        and level__0002 __strm__ =
          match
            level__0002_matcher __strm__[@llk.first_follow "\"[\" | UIDENT \"NONA\" | UIDENT \"RIGHTA\" | UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\""]
          with
            0 -> (parser [< x__0057 = assoc >] -> Some x__0057) __strm__
          | 1 -> (parser [< >] -> None) __strm__
          | _ -> raise Stream.Failure
        and level__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFTA") -> 0
          | Some ("UIDENT", "NONA") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "RIGHTA") -> 0
          | Some ("", "[") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[x__0057 = assoc] or [<empty>] expected after [lab = level__0001] (in [level])")
        and level_list __strm__ =
          match level_list_matcher __strm__[@llk.first_follow "\"[\""] with
            0 ->
              (parser
                 [< '"", "[";
                    ll =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[ll = level_list__0001] expected after ['['] (in [level_list])"
                        level_list__0001;
                    '"", "]" >] ->
                   ll)
                __strm__
          | _ -> raise Stream.Failure
        and level_list_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and level_list__0001 __strm__ =
          match
            level_list__0001_regexp __strm__[@llk.regexp "#0 | (\"[\" | UIDENT \"NONA\" | UIDENT \"RIGHTA\" | UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\" | STRING) #1"]
          with
            Some (_, 0) -> (parser [< >] -> []) __strm__
          | Some (_, 1) -> (parser [< a = level_list__0002 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and level_list__0001_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 0) in
            match must_peek_nth (ofs + 1) strm with
              Some ("", "[") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "GREEDY") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "LEFTA") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "NONA") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "NONGREEDY") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "RIGHTA") -> q0001 lastf (ofs + 1)
            | Some ("STRING", _) -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and level_list__0002 __strm__ =
          match
            level_list__0002_matcher __strm__[@llk.first_follow "\"[\" | UIDENT \"NONA\" | UIDENT \"RIGHTA\" | UIDENT \"GREEDY\" | UIDENT \"LEFTA\" | UIDENT \"NONGREEDY\" | STRING"]
          with
            0 ->
              (parser
                 [< x__0027 = level;
                    y__0018 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0018 = level_list__0003] expected after [x__0027 = level] (in [level_list])"
                        level_list__0003 >] ->
                   x__0027 :: y__0018)
                __strm__
          | _ -> raise Stream.Failure
        and level_list__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFTA") -> 0
          | Some ("UIDENT", "NONA") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "RIGHTA") -> 0
          | Some ("STRING", _) -> 0
          | Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and level_list__0003 __strm__ =
          match
            level_list__0003_matcher __strm__[@llk.first_follow "\"]\" | \"|\""]
          with
            0 ->
              (parser
                 [< x__0028 = level_list__0004;
                    y__0019 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0019 = level_list__0003] expected after [x__0028 = level_list__0004] (in [level_list])"
                        level_list__0003 >] ->
                   x__0028 :: y__0019)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and level_list__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and level_list__0004 __strm__ =
          match
            level_list__0004_matcher __strm__[@llk.first_follow "\"|\""]
          with
            0 ->
              (parser
                 [< '"", "|";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0018 = level] expected after ['|'] (in [level_list])"
                        level >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and level_list__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | _ -> raise Stream.Failure
        and paren_pattern __strm__ =
          match paren_pattern_matcher __strm__[@llk.first_follow "\"(\""] with
            0 ->
              (parser bp
                 [< '"", "(";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = paren_pattern__0001] expected after ['('] (in [paren_pattern])"
                        paren_pattern__0001;
                    '"", ")" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   MLast.PaTup (loc, Ploc.VaVal l))
                __strm__
          | _ -> raise Stream.Failure
        and paren_pattern_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | _ -> raise Stream.Failure
        and paren_pattern__0001 __strm__ =
          match
            paren_pattern__0001_matcher __strm__[@llk.first_follow "LIDENT | \"(\" | \"_\""]
          with
            0 ->
              (parser
                 [< x__0029 = pattern;
                    y__0020 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0020 = paren_pattern__0002] expected after [x__0029 = pattern] (in [paren_pattern])"
                        paren_pattern__0002 >] ->
                   x__0029 :: y__0020)
                __strm__
          | _ -> raise Stream.Failure
        and paren_pattern__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "_") -> 0
          | _ -> raise Stream.Failure
        and paren_pattern__0002 __strm__ =
          match
            paren_pattern__0002_matcher __strm__[@llk.first_follow "\",\" | \")\""]
          with
            0 ->
              (parser
                 [< x__0030 = paren_pattern__0003;
                    y__0021 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0021 = paren_pattern__0002] expected after [x__0030 = paren_pattern__0003] (in [paren_pattern])"
                        paren_pattern__0002 >] ->
                   x__0030 :: y__0021)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and paren_pattern__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | Some ("", ")") -> 1
          | _ -> raise Stream.Failure
        and paren_pattern__0003 __strm__ =
          match
            paren_pattern__0003_matcher __strm__[@llk.first_follow "\",\""]
          with
            0 ->
              (parser
                 [< '"", ",";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0020 = pattern] expected after [','] (in [paren_pattern])"
                        pattern >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and paren_pattern__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
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
            psymbol_regexp __strm__[@llk.regexp "\"_\" #0 | LIDENT \"=\" #1 | LIDENT \"[\" #2 | \"(\" (LIDENT | \"(\" | \"_\" | \",\" | \")\")* \"=\" #3 | (LIDENT | \"[\" | \"(\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\") #4"]
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
                        ~msg:"[args = psymbol__0001] expected after [PREDICT check_lident_lbracket; p = LIDENT] (in [psymbol])"
                        psymbol__0001;
                    lev =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[lev = psymbol__0005] expected after [PREDICT check_lident_lbracket; p = LIDENT; args = psymbol__0001] (in [psymbol])"
                        psymbol__0005 >] ep ->
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
            | Some ("UIDENT", "ANTI") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "FLAG") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "GREEDY") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "LEFT_ASSOC") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "LIST0") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "LIST1") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "NEXT") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "NONGREEDY") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "OPT") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "PREDICT") ->
                let lastf = Some (ofs, 2) in q0002 lastf (ofs + 1)
            | Some ("UIDENT", "PRIORITY") ->
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
        and psymbol__0001 __strm__ =
          match
            psymbol__0001_matcher __strm__[@llk.first_follow "\"[\" | \"]\" | \";\" | \"|\" | UIDENT \"LEVEL\" | \"->\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = psymbol__0003] expected after [PREDICT check_lident_lbracket; p = LIDENT; '['] (in [psymbol])"
                        psymbol__0003;
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and psymbol__0001_matcher __strm__ =
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
        and psymbol__0002 __strm__ =
          match
            psymbol__0002_matcher __strm__[@llk.first_follow "UIDENT \"LEVEL\""]
          with
            0 -> (parser [< '"UIDENT", "LEVEL"; '"STRING", s >] -> s) __strm__
          | _ -> raise Stream.Failure
        and psymbol__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | _ -> raise Stream.Failure
        and psymbol__0003 __strm__ =
          match
            psymbol__0003_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | INT | QUOTATION | \"{\""]
          with
            0 ->
              (parser
                 [< x__0031 = Grammar.Entry.parse_token_stream expr;
                    y__0022 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0022 = psymbol__0004] expected after [x__0031 = expr] (in [psymbol])"
                        psymbol__0004 >] ->
                   x__0031 :: y__0022)
                __strm__
          | _ -> raise Stream.Failure
        and psymbol__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("INT", _) -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("QUOTATION", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "{") -> 0
          | _ -> raise Stream.Failure
        and psymbol__0004 __strm__ =
          match
            psymbol__0004_matcher __strm__[@llk.first_follow "\",\" | \"]\""]
          with
            0 ->
              (parser
                 [< x__0032 = psymbol__0006;
                    y__0023 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0023 = psymbol__0004] expected after [x__0032 = psymbol__0006] (in [psymbol])"
                        psymbol__0004 >] ->
                   x__0032 :: y__0023)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and psymbol__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and psymbol__0005 __strm__ =
          match
            psymbol__0005_matcher __strm__[@llk.first_follow "\"]\" | \";\" | \"|\" | UIDENT \"LEVEL\" | \"->\""]
          with
            0 ->
              (parser [< x__0058 = psymbol__0002 >] -> Some x__0058) __strm__
          | 1 -> (parser [< >] -> None) __strm__
          | _ -> raise Stream.Failure
        and psymbol__0005_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | Some ("", "->") -> 1
          | Some ("", ";") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ ->
              raise
                (Stream.Error
                   "[x__0058 = psymbol__0002] or [<empty>] expected after [PREDICT check_lident_lbracket; p = LIDENT; args = psymbol__0001] (in [psymbol])")
        and psymbol__0006 __strm__ =
          match psymbol__0006_matcher __strm__[@llk.first_follow "\",\""] with
            0 ->
              (parser
                 [< '"", ",";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0022 = expr] expected after [','] (in [psymbol])"
                        (Grammar.Entry.parse_token_stream expr) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and psymbol__0006_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | _ -> raise Stream.Failure
        and regexp __strm__ =
          match
            regexp_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"~\" | \"let\""]
          with
            0 -> (parser [< a = e6 >] -> a) __strm__
          | _ -> raise Stream.Failure
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
        and regexp_entry __strm__ =
          match regexp_entry_matcher __strm__[@llk.first_follow "LIDENT"] with
            0 ->
              (parser
                 [< '"LIDENT", n; '"", "=";
                    r =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[r = regexp] expected after [n = LIDENT; '='] (in [regexp_entry])"
                        regexp;
                    '"", ";" >] ->
                   Name.mk n, r)
                __strm__
          | _ -> raise Stream.Failure
        and regexp_entry_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and regexps __strm__ =
          match
            regexps_matcher __strm__[@llk.first_follow "UIDENT \"REGEXPS\""]
          with
            0 ->
              (parser
                 [< '"UIDENT", "REGEXPS"; '"", ":";
                    rl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[rl = regexps__0001] expected after [UIDENT 'REGEXPS'; ':'] (in [regexps])"
                        regexps__0001;
                    '"", "END"; '"", ";" >] ->
                   rl)
                __strm__
          | _ -> raise Stream.Failure
        and regexps_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "REGEXPS") -> 0
          | _ -> raise Stream.Failure
        and regexps__0001 __strm__ =
          match
            regexps__0001_matcher __strm__[@llk.first_follow "LIDENT"]
          with
            0 ->
              (parser
                 [< x__0033 = regexp_entry;
                    y__0024 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0024 = regexps__0002] expected after [x__0033 = regexp_entry] (in [regexps])"
                        regexps__0002 >] ->
                   x__0033 :: y__0024)
                __strm__
          | _ -> raise Stream.Failure
        and regexps__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | _ -> raise Stream.Failure
        and regexps__0002 __strm__ =
          match
            regexps__0002_matcher __strm__[@llk.first_follow "LIDENT | \"END\""]
          with
            0 ->
              (parser
                 [< x__0034 = regexp_entry;
                    y__0025 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0025 = regexps__0002] expected after [x__0034 = regexp_entry] (in [regexps])"
                        regexps__0002 >] ->
                   x__0034 :: y__0025)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and regexps__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("", "END") -> 1
          | _ -> raise Stream.Failure
        and rule __strm__ =
          match
            rule_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\""]
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
                 [< psl = rule__0002;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0003 = rule__0001[<expr>]] expected after [psl = rule__0002] (in [rule])"
                        (rule__0001 psl) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and rule_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "->") -> 0
          | Some ("UIDENT", "ANTI") -> 1
          | Some ("UIDENT", "FLAG") -> 1
          | Some ("UIDENT", "GREEDY") -> 1
          | Some ("UIDENT", "LEFT_ASSOC") -> 1
          | Some ("UIDENT", "LIST0") -> 1
          | Some ("UIDENT", "LIST1") -> 1
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "NONGREEDY") -> 1
          | Some ("UIDENT", "OPT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "PRIORITY") -> 1
          | Some ("UIDENT", "SELF") -> 1
          | Some ("UIDENT", "V") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "(") -> 1
          | Some ("", "[") -> 1
          | Some ("", "_") -> 1
          | _ -> raise Stream.Failure
        and rule__0001 psl __strm__ =
          match
            rule__0001_matcher __strm__[@llk.first_follow "\"]\" | \"|\" | \"->\""]
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
        and rule__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "->") -> 0
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ ->
              raise
                (Stream.Error
                   "['->'] or [<empty>] expected after [psl = LIST1 psymbol SEP ';'] (in [rule])")
        and rule__0002 __strm__ =
          match
            rule__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\""]
          with
            0 ->
              (parser
                 [< x__0035 = psymbol;
                    y__0026 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0026 = rule__0003] expected after [x__0035 = psymbol] (in [rule])"
                        rule__0003 >] ->
                   x__0035 :: y__0026)
                __strm__
          | _ -> raise Stream.Failure
        and rule__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "ANTI") -> 0
          | Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 0
          | Some ("UIDENT", "LIST0") -> 0
          | Some ("UIDENT", "LIST1") -> 0
          | Some ("UIDENT", "NEXT") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "OPT") -> 0
          | Some ("UIDENT", "PREDICT") -> 0
          | Some ("UIDENT", "PRIORITY") -> 0
          | Some ("UIDENT", "SELF") -> 0
          | Some ("UIDENT", "V") -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | _ -> raise Stream.Failure
        and rule__0003 __strm__ =
          match
            rule__0003_matcher __strm__[@llk.first_follow "\"]\" | \";\" | \"|\" | \"->\""]
          with
            0 ->
              (parser
                 [< x__0036 = rule__0004;
                    y__0027 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0027 = rule__0003] expected after [x__0036 = rule__0004] (in [rule])"
                        rule__0003 >] ->
                   x__0036 :: y__0027)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and rule__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ";") -> 0
          | Some ("", "->") -> 1
          | Some ("", "]") -> 1
          | Some ("", "|") -> 1
          | _ -> raise Stream.Failure
        and rule__0004 __strm__ =
          match rule__0004_matcher __strm__[@llk.first_follow "\";\""] with
            0 ->
              (parser
                 [< '"", ";";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0026 = psymbol] expected after [';'] (in [rule])"
                        psymbol >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and rule__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ";") -> 0
          | _ -> raise Stream.Failure
        and rule_list __strm__ =
          match rule_list_matcher __strm__[@llk.first_follow "\"[\""] with
            0 ->
              (parser
                 [< '"", "[";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0004 = rule_list__0001] expected after ['['] (in [rule_list])"
                        rule_list__0001 >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and rule_list_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and rule_list__0001 __strm__ =
          match
            rule_list__0001_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | \"]\" | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\""]
          with
            0 ->
              (parser bp
                 [< '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {au_loc = loc; au_rules = []})
                __strm__
          | 1 ->
              (parser bp
                 [< rules = rule_list__0002; '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   {au_loc = loc; au_rules = rules})
                __strm__
          | _ -> raise Stream.Failure
        and rule_list__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "]") -> 0
          | Some ("UIDENT", "ANTI") -> 1
          | Some ("UIDENT", "FLAG") -> 1
          | Some ("UIDENT", "GREEDY") -> 1
          | Some ("UIDENT", "LEFT_ASSOC") -> 1
          | Some ("UIDENT", "LIST0") -> 1
          | Some ("UIDENT", "LIST1") -> 1
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "NONGREEDY") -> 1
          | Some ("UIDENT", "OPT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "PRIORITY") -> 1
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
                   "[']'] or [rules = rule_list__0002] expected after ['['] (in [rule_list])")
        and rule_list__0002 __strm__ =
          match
            rule_list__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\""]
          with
            0 ->
              (parser
                 [< x__0037 = rule;
                    y__0028 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0028 = rule_list__0003] expected after [x__0037 = rule] (in [rule_list])"
                        rule_list__0003 >] ->
                   x__0037 :: y__0028)
                __strm__
          | _ -> raise Stream.Failure
        and rule_list__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "ANTI") -> 0
          | Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 0
          | Some ("UIDENT", "LIST0") -> 0
          | Some ("UIDENT", "LIST1") -> 0
          | Some ("UIDENT", "NEXT") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "OPT") -> 0
          | Some ("UIDENT", "PREDICT") -> 0
          | Some ("UIDENT", "PRIORITY") -> 0
          | Some ("UIDENT", "SELF") -> 0
          | Some ("UIDENT", "V") -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "->") -> 0
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | _ -> raise Stream.Failure
        and rule_list__0003 __strm__ =
          match
            rule_list__0003_matcher __strm__[@llk.first_follow "\"]\" | \"|\""]
          with
            0 ->
              (parser
                 [< x__0038 = rule_list__0004;
                    y__0029 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0029 = rule_list__0003] expected after [x__0038 = rule_list__0004] (in [rule_list])"
                        rule_list__0003 >] ->
                   x__0038 :: y__0029)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and rule_list__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and rule_list__0004 __strm__ =
          match
            rule_list__0004_matcher __strm__[@llk.first_follow "\"|\""]
          with
            0 ->
              (parser
                 [< '"", "|";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0028 = rule] expected after ['|'] (in [rule_list])"
                        rule >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and rule_list__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | _ -> raise Stream.Failure
        and sep_opt_sep __strm__ =
          match
            sep_opt_sep_matcher __strm__[@llk.first_follow "UIDENT \"SEP\""]
          with
            0 ->
              (parser
                 [< '"UIDENT", ("SEP" as sep);
                    t =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[t = symbol] expected after [sep = UIDENT 'SEP'] (in [sep_opt_sep])"
                        symbol;
                    b =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[b = sep_opt_sep__0002] expected after [sep = UIDENT 'SEP'; t = symbol] (in [sep_opt_sep])"
                        sep_opt_sep__0002 >] ->
                   t, b)
                __strm__
          | _ -> raise Stream.Failure
        and sep_opt_sep_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "SEP") -> 0
          | _ -> raise Stream.Failure
        and sep_opt_sep__0001 __strm__ =
          match
            sep_opt_sep__0001_matcher __strm__[@llk.first_follow "UIDENT \"OPT_SEP\""]
          with
            0 -> (parser [< '"UIDENT", "OPT_SEP" >] -> ()) __strm__
          | _ -> raise Stream.Failure
        and sep_opt_sep__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "OPT_SEP") -> 0
          | _ -> raise Stream.Failure
        and sep_opt_sep__0002 __strm__ =
          match
            sep_opt_sep__0002_regexp __strm__[@llk.regexp "#1 | UIDENT \"OPT_SEP\" #0"]
          with
            Some (_, 0) ->
              (parser [< _ = sep_opt_sep__0001 >] -> true) __strm__
          | Some (_, 1) -> (parser [< >] -> false) __strm__
          | _ -> raise Stream.Failure
        and sep_opt_sep__0002_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 1) in
            match must_peek_nth (ofs + 1) strm with
              Some ("UIDENT", "OPT_SEP") -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 0) in lastf in
          q0000 None 0
        and symbol __strm__ =
          match
            symbol_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\""]
          with
            0 -> (parser [< a = symbol__0002 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "ANTI") -> 0
          | Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 0
          | Some ("UIDENT", "LIST0") -> 0
          | Some ("UIDENT", "LIST1") -> 0
          | Some ("UIDENT", "NEXT") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "OPT") -> 0
          | Some ("UIDENT", "PREDICT") -> 0
          | Some ("UIDENT", "PRIORITY") -> 0
          | Some ("UIDENT", "SELF") -> 0
          | Some ("UIDENT", "V") -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | _ -> raise Stream.Failure
        and symbol__0002 __strm__ =
          match
            symbol__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\""]
          with
            0 ->
              (parser
                 [< g = symbol__0006;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0005 = symbol__0007[<expr>]] expected after [g = symbol__0006] (in [symbol])"
                        (symbol__0007 g) >] ->
                   a)
                __strm__
          | 1 -> (parser [< a = symbol__0003 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol__0002_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 0
          | Some ("UIDENT", "LIST0") -> 0
          | Some ("UIDENT", "LIST1") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "OPT") -> 0
          | Some ("UIDENT", "ANTI") -> 1
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "PRIORITY") -> 1
          | Some ("UIDENT", "SELF") -> 1
          | Some ("UIDENT", "V") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "(") -> 1
          | Some ("", "[") -> 1
          | _ -> raise Stream.Failure
        and symbol__0003 __strm__ =
          match
            symbol__0003_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"ANTI\" | UIDENT \"NEXT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\""]
          with
            0 ->
              (parser bp
                 [< '"UIDENT", "V";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0003] expected after [UIDENT 'V'] (in [symbol])"
                        symbol__0003;
                    al =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[al = symbol__0014] expected after [UIDENT 'V'; s = symbol__0003] (in [symbol])"
                        symbol__0014 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASvala (loc, s, al))
                __strm__
          | 1 -> (parser [< a = symbol__0004 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol__0003_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "V") -> 0
          | Some ("UIDENT", "ANTI") -> 1
          | Some ("UIDENT", "NEXT") -> 1
          | Some ("UIDENT", "PREDICT") -> 1
          | Some ("UIDENT", "PRIORITY") -> 1
          | Some ("UIDENT", "SELF") -> 1
          | Some ("LIDENT", _) -> 1
          | Some ("STRING", _) -> 1
          | Some ("UIDENT", _) -> 1
          | Some ("", "(") -> 1
          | Some ("", "[") -> 1
          | _ -> raise Stream.Failure
        and symbol__0004 __strm__ =
          match
            symbol__0004_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | UIDENT | STRING | UIDENT \"ANTI\" | UIDENT \"NEXT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\""]
          with
            0 ->
              (parser
                 [< '"", "(";
                    s_t =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s_t = symbol__0002] expected after ['('] (in [symbol])"
                        symbol__0002;
                    '"", ")";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0006 = symbol__0008[<expr>]] expected after ['('; s_t = symbol__0002; ')'] (in [symbol])"
                        (symbol__0008 s_t) >] ->
                   a)
                __strm__
          | 1 ->
              (parser bp
                 [< '"", "[";
                    rl =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[rl = symbol__0015] expected after ['['] (in [symbol])"
                        symbol__0015;
                    '"", "]" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASrules (loc, {au_loc = loc; au_rules = rl}))
                __strm__
          | 2 ->
              (parser bp
                 [< '"UIDENT", "ANTI";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = symbol__0016] expected after [UIDENT 'ANTI'] (in [symbol])"
                        symbol__0016 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASanti (loc, l))
                __strm__
          | 3 ->
              (parser bp
                 [< '"UIDENT", "NEXT";
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = symbol__0009] expected after [UIDENT 'NEXT'] (in [symbol])"
                        symbol__0009 >] ep ->
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
                 [< '"UIDENT", "PRIORITY"; '"INT", n >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASpriority (loc, int_of_string n))
                __strm__
          | 6 ->
              (parser bp
                 [< '"UIDENT", "SELF";
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = symbol__0010] expected after [UIDENT 'SELF'] (in [symbol])"
                        symbol__0010 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASself (loc, args))
                __strm__
          | 7 ->
              (parser bp
                 [< '"STRING", e >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASkeyw (loc, e))
                __strm__
          | 8 ->
              (parser bp
                 [< '"LIDENT", id;
                    args =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[args = symbol__0011] expected after [id = LIDENT] (in [symbol])"
                        symbol__0011;
                    lev =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[lev = symbol__0026] expected after [id = LIDENT; args = symbol__0011] (in [symbol])"
                        symbol__0026 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASnterm (loc, Name.mk id, args, lev))
                __strm__
          | 9 ->
              (parser
                 [< '"UIDENT", x;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0007 = symbol__0013[<expr>]] expected after [x = UIDENT] (in [symbol])"
                        (symbol__0013 x) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0004_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "(") -> 0
          | Some ("", "[") -> 1
          | Some ("UIDENT", "ANTI") -> 2
          | Some ("UIDENT", "NEXT") -> 3
          | Some ("UIDENT", "PREDICT") -> 4
          | Some ("UIDENT", "PRIORITY") -> 5
          | Some ("UIDENT", "SELF") -> 6
          | Some ("STRING", _) -> 7
          | Some ("LIDENT", _) -> 8
          | Some ("UIDENT", _) -> 9
          | _ -> raise Stream.Failure
        and symbol__0006 __strm__ =
          match
            symbol__0006_matcher __strm__[@llk.first_follow "UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"OPT\""]
          with
            0 -> (parser [< '"UIDENT", "GREEDY" >] -> true) __strm__
          | 1 -> (parser [< '"UIDENT", "NONGREEDY" >] -> false) __strm__
          | 2 -> (parser [< >] -> true) __strm__
          | _ -> raise Stream.Failure
        and symbol__0006_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 1
          | Some ("UIDENT", "FLAG") -> 2
          | Some ("UIDENT", "LEFT_ASSOC") -> 2
          | Some ("UIDENT", "LIST0") -> 2
          | Some ("UIDENT", "LIST1") -> 2
          | Some ("UIDENT", "OPT") -> 2
          | _ -> raise Stream.Failure
        and symbol__0007 g __strm__ =
          match
            symbol__0007_matcher __strm__[@llk.first_follow "UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"OPT\""]
          with
            0 ->
              (parser bp
                 [< '"UIDENT", "FLAG";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0003] expected after [g = symbol__0006; UIDENT 'FLAG'] (in [symbol])"
                        symbol__0003 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASflag (loc, g, s))
                __strm__
          | 1 ->
              (parser bp
                 [< '"UIDENT", "LEFT_ASSOC";
                    s1 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s1 = symbol__0003] expected after [g = symbol__0006; UIDENT 'LEFT_ASSOC'] (in [symbol])"
                        symbol__0003;
                    '"UIDENT", "ACCUMULATE";
                    s2 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s2 = symbol__0003] expected after [g = symbol__0006; UIDENT 'LEFT_ASSOC'; s1 = symbol__0003; UIDENT 'ACCUMULATE'] (in [symbol])"
                        symbol__0003;
                    '"UIDENT", "WITH";
                    e =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[e = expr_LEVEL_simple] expected after [g = symbol__0006; UIDENT 'LEFT_ASSOC'; s1 = symbol__0003; UIDENT 'ACCUMULATE'; s2 = symbol__0003; UIDENT 'WITH'] (in [symbol])"
                        (Grammar.Entry.parse_token_stream
                           expr_LEVEL_simple) >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASleft_assoc (loc, g, s1, s2, e))
                __strm__
          | 2 ->
              (parser bp
                 [< '"UIDENT", "LIST0";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0003] expected after [g = symbol__0006; UIDENT 'LIST0'] (in [symbol])"
                        symbol__0003;
                    sep =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[sep = symbol__0028] expected after [g = symbol__0006; UIDENT 'LIST0'; s = symbol__0003] (in [symbol])"
                        symbol__0028 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASlist (loc, g, LML_0, s, sep))
                __strm__
          | 3 ->
              (parser bp
                 [< '"UIDENT", "LIST1";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0003] expected after [g = symbol__0006; UIDENT 'LIST1'] (in [symbol])"
                        symbol__0003;
                    sep =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[sep = symbol__0029] expected after [g = symbol__0006; UIDENT 'LIST1'; s = symbol__0003] (in [symbol])"
                        symbol__0029 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASlist (loc, g, LML_1, s, sep))
                __strm__
          | 4 ->
              (parser bp
                 [< '"UIDENT", "OPT";
                    s =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[s = symbol__0003] expected after [g = symbol__0006; UIDENT 'OPT'] (in [symbol])"
                        symbol__0003 >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASopt (loc, g, s))
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0007_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 1
          | Some ("UIDENT", "LIST0") -> 2
          | Some ("UIDENT", "LIST1") -> 3
          | Some ("UIDENT", "OPT") -> 4
          | _ ->
              raise
                (Stream.Error
                   "[UIDENT 'FLAG'] or [UIDENT 'LEFT_ASSOC'] or [UIDENT 'LIST0'] or [UIDENT 'LIST1'] or [UIDENT 'OPT'] expected after [g = symbol__0006] (in [symbol])")
        and symbol__0008 s_t __strm__ =
          match
            symbol__0008_matcher __strm__[@llk.first_follow "\")\" | STRING | \"]\" | \";\" | \"?\" | \"|\" | \"->\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser bp
                 [< '"", "?" >] ep ->
                   let loc = Grammar.loc_of_token_interval bp ep in
                   ASsyntactic (loc, s_t))
                __strm__
          | 1 -> (parser [< >] -> s_t) __strm__
          | _ -> raise Stream.Failure
        and symbol__0008_matcher __strm__ =
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
                   "['?'] or [<empty>] expected after ['('; s_t = symbol__0002; ')'] (in [symbol])")
        and symbol__0009 __strm__ =
          match
            symbol__0009_matcher __strm__[@llk.first_follow "\"[\" | \")\" | STRING | \"]\" | \";\" | \"|\" | \"->\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = symbol__0020] expected after [UIDENT 'NEXT'; '['] (in [symbol])"
                        symbol__0020;
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0009_matcher __strm__ =
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
        and symbol__0010 __strm__ =
          match
            symbol__0010_matcher __strm__[@llk.first_follow "\"[\" | \")\" | STRING | \"]\" | \";\" | \"|\" | \"->\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = symbol__0022] expected after [UIDENT 'SELF'; '['] (in [symbol])"
                        symbol__0022;
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0010_matcher __strm__ =
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
        and symbol__0011 __strm__ =
          match
            symbol__0011_matcher __strm__[@llk.first_follow "\"[\" | \")\" | STRING | \"]\" | \";\" | \"|\" | UIDENT \"LEVEL\" | \"->\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser
                 [< '"", "[";
                    l =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[l = symbol__0024] expected after [id = LIDENT; '['] (in [symbol])"
                        symbol__0024;
                    '"", "]" >] ->
                   l)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0011_matcher __strm__ =
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
        and symbol__0012 __strm__ =
          match
            symbol__0012_matcher __strm__[@llk.first_follow "UIDENT \"LEVEL\""]
          with
            0 -> (parser [< '"UIDENT", "LEVEL"; '"STRING", s >] -> s) __strm__
          | _ -> raise Stream.Failure
        and symbol__0012_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
          | _ -> raise Stream.Failure
        and symbol__0013 x __strm__ =
          match
            symbol__0013_matcher __strm__[@llk.first_follow "\")\" | STRING | \"]\" | \";\" | \"|\" | \"->\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\" | \"/\""]
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
        and symbol__0013_matcher __strm__ =
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
        and symbol__0014 __strm__ =
          match
            symbol__0014_regexp __strm__[@llk.regexp "#0 | STRING #1"]
          with
            Some (_, 0) -> (parser [< >] -> []) __strm__
          | Some (_, 1) ->
              (parser
                 [< '"STRING", x__0039;
                    y__0030 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0030 = symbol__0014] expected after [x__0039 = STRING] (in [symbol])"
                        symbol__0014 >] ->
                   x__0039 :: y__0030)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0014_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 0) in
            match must_peek_nth (ofs + 1) strm with
              Some ("STRING", _) -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and symbol__0015 __strm__ =
          match
            symbol__0015_regexp __strm__[@llk.regexp "#0 | (LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\") #1"]
          with
            Some (_, 0) -> (parser [< >] -> []) __strm__
          | Some (_, 1) -> (parser [< a = symbol__0018 >] -> a) __strm__
          | _ -> raise Stream.Failure
        and symbol__0015_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 0) in
            match must_peek_nth (ofs + 1) strm with
              Some ("", "(") -> q0001 lastf (ofs + 1)
            | Some ("", "->") -> q0001 lastf (ofs + 1)
            | Some ("", "[") -> q0001 lastf (ofs + 1)
            | Some ("", "_") -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", "ANTI") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "FLAG") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "GREEDY") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "LEFT_ASSOC") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "LIST0") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "LIST1") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "NEXT") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "NONGREEDY") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "OPT") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "PREDICT") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "PRIORITY") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "SELF") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("UIDENT", "V") ->
                let lastf = Some (ofs, 1) in q0001 lastf (ofs + 1)
            | Some ("LIDENT", _) -> q0001 lastf (ofs + 1)
            | Some ("STRING", _) -> q0001 lastf (ofs + 1)
            | Some ("UIDENT", _) -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and symbol__0016 __strm__ =
          match symbol__0016_matcher __strm__[@llk.first_follow "STRING"] with
            0 ->
              (parser
                 [< '"STRING", x__0041;
                    y__0032 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0032 = symbol__0017] expected after [x__0041 = STRING] (in [symbol])"
                        symbol__0017 >] ->
                   x__0041 :: y__0032)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0016_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("STRING", _) -> 0
          | _ -> raise Stream.Failure
        and symbol__0017 __strm__ =
          match
            symbol__0017_regexp __strm__[@llk.regexp "#0 | STRING #1"]
          with
            Some (_, 0) -> (parser [< >] -> []) __strm__
          | Some (_, 1) ->
              (parser
                 [< '"STRING", x__0042;
                    y__0033 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0033 = symbol__0017] expected after [x__0042 = STRING] (in [symbol])"
                        symbol__0017 >] ->
                   x__0042 :: y__0033)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0017_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 0) in
            match must_peek_nth (ofs + 1) strm with
              Some ("STRING", _) -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and symbol__0018 __strm__ =
          match
            symbol__0018_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | UIDENT | UIDENT \"GREEDY\" | UIDENT \"NONGREEDY\" | STRING | UIDENT \"ANTI\" | UIDENT \"FLAG\" | UIDENT \"LEFT_ASSOC\" | UIDENT \"LIST0\" | UIDENT \"LIST1\" | UIDENT \"NEXT\" | UIDENT \"OPT\" | UIDENT \"PREDICT\" | UIDENT \"PRIORITY\" | UIDENT \"SELF\" | UIDENT \"V\" | \"->\""]
          with
            0 ->
              (parser
                 [< x__0043 = rule;
                    y__0034 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0034 = symbol__0019] expected after [x__0043 = rule] (in [symbol])"
                        symbol__0019 >] ->
                   x__0043 :: y__0034)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0018_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "ANTI") -> 0
          | Some ("UIDENT", "FLAG") -> 0
          | Some ("UIDENT", "GREEDY") -> 0
          | Some ("UIDENT", "LEFT_ASSOC") -> 0
          | Some ("UIDENT", "LIST0") -> 0
          | Some ("UIDENT", "LIST1") -> 0
          | Some ("UIDENT", "NEXT") -> 0
          | Some ("UIDENT", "NONGREEDY") -> 0
          | Some ("UIDENT", "OPT") -> 0
          | Some ("UIDENT", "PREDICT") -> 0
          | Some ("UIDENT", "PRIORITY") -> 0
          | Some ("UIDENT", "SELF") -> 0
          | Some ("UIDENT", "V") -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 0
          | Some ("UIDENT", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "->") -> 0
          | Some ("", "[") -> 0
          | Some ("", "_") -> 0
          | _ -> raise Stream.Failure
        and symbol__0019 __strm__ =
          match
            symbol__0019_matcher __strm__[@llk.first_follow "\"]\" | \"|\""]
          with
            0 ->
              (parser
                 [< x__0044 = symbol__0027;
                    y__0035 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0035 = symbol__0019] expected after [x__0044 = symbol__0027] (in [symbol])"
                        symbol__0019 >] ->
                   x__0044 :: y__0035)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0019_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and symbol__0020 __strm__ =
          match
            symbol__0020_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | INT | QUOTATION | \"{\""]
          with
            0 ->
              (parser
                 [< x__0045 = Grammar.Entry.parse_token_stream expr;
                    y__0036 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0036 = symbol__0021] expected after [x__0045 = expr] (in [symbol])"
                        symbol__0021 >] ->
                   x__0045 :: y__0036)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0020_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("INT", _) -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("QUOTATION", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "{") -> 0
          | _ -> raise Stream.Failure
        and symbol__0021 __strm__ =
          match
            symbol__0021_matcher __strm__[@llk.first_follow "\",\" | \"]\""]
          with
            0 ->
              (parser
                 [< x__0046 = symbol__0030;
                    y__0037 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0037 = symbol__0021] expected after [x__0046 = symbol__0030] (in [symbol])"
                        symbol__0021 >] ->
                   x__0046 :: y__0037)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0021_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and symbol__0022 __strm__ =
          match
            symbol__0022_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | INT | QUOTATION | \"{\""]
          with
            0 ->
              (parser
                 [< x__0047 = Grammar.Entry.parse_token_stream expr;
                    y__0038 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0038 = symbol__0023] expected after [x__0047 = expr] (in [symbol])"
                        symbol__0023 >] ->
                   x__0047 :: y__0038)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0022_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("INT", _) -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("QUOTATION", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "{") -> 0
          | _ -> raise Stream.Failure
        and symbol__0023 __strm__ =
          match
            symbol__0023_matcher __strm__[@llk.first_follow "\",\" | \"]\""]
          with
            0 ->
              (parser
                 [< x__0048 = symbol__0031;
                    y__0039 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0039 = symbol__0023] expected after [x__0048 = symbol__0031] (in [symbol])"
                        symbol__0023 >] ->
                   x__0048 :: y__0039)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0023_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and symbol__0024 __strm__ =
          match
            symbol__0024_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | INT | QUOTATION | \"{\""]
          with
            0 ->
              (parser
                 [< x__0049 = Grammar.Entry.parse_token_stream expr;
                    y__0040 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0040 = symbol__0025] expected after [x__0049 = expr] (in [symbol])"
                        symbol__0025 >] ->
                   x__0049 :: y__0040)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0024_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("INT", _) -> 0
          | Some ("LIDENT", _) -> 0
          | Some ("QUOTATION", _) -> 0
          | Some ("", "(") -> 0
          | Some ("", "[") -> 0
          | Some ("", "{") -> 0
          | _ -> raise Stream.Failure
        and symbol__0025 __strm__ =
          match
            symbol__0025_matcher __strm__[@llk.first_follow "\",\" | \"]\""]
          with
            0 ->
              (parser
                 [< x__0050 = symbol__0032;
                    y__0041 =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0041 = symbol__0025] expected after [x__0050 = symbol__0032] (in [symbol])"
                        symbol__0025 >] ->
                   x__0050 :: y__0041)
                __strm__
          | 1 -> (parser [< >] -> []) __strm__
          | _ -> raise Stream.Failure
        and symbol__0025_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | Some ("", "]") -> 1
          | _ -> raise Stream.Failure
        and symbol__0026 __strm__ =
          match
            symbol__0026_matcher __strm__[@llk.first_follow "\")\" | STRING | \"]\" | \";\" | \"|\" | UIDENT \"LEVEL\" | \"->\" | UIDENT \"SEP\" | UIDENT \"OPT_SEP\" | UIDENT \"ACCUMULATE\" | UIDENT \"WITH\""]
          with
            0 ->
              (parser [< x__0059 = symbol__0012 >] -> Some x__0059) __strm__
          | 1 -> (parser [< >] -> None) __strm__
          | _ -> raise Stream.Failure
        and symbol__0026_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("UIDENT", "LEVEL") -> 0
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
                   "[x__0059 = symbol__0012] or [<empty>] expected after [id = LIDENT; args = symbol__0011] (in [symbol])")
        and symbol__0027 __strm__ =
          match symbol__0027_matcher __strm__[@llk.first_follow "\"|\""] with
            0 ->
              (parser
                 [< '"", "|";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0034 = rule] expected after ['|'] (in [symbol])"
                        rule >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0027_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", "|") -> 0
          | _ -> raise Stream.Failure
        and symbol__0028 __strm__ =
          match
            symbol__0028_regexp __strm__[@llk.regexp "#0 | UIDENT \"SEP\" #1"]
          with
            Some (_, 0) -> (parser [< >] -> None) __strm__
          | Some (_, 1) ->
              (parser [< x__0062 = sep_opt_sep >] -> Some x__0062) __strm__
          | _ -> raise Stream.Failure
        and symbol__0028_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 0) in
            match must_peek_nth (ofs + 1) strm with
              Some ("UIDENT", "SEP") -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and symbol__0029 __strm__ =
          match
            symbol__0029_regexp __strm__[@llk.regexp "#0 | UIDENT \"SEP\" #1"]
          with
            Some (_, 0) -> (parser [< >] -> None) __strm__
          | Some (_, 1) ->
              (parser [< x__0063 = sep_opt_sep >] -> Some x__0063) __strm__
          | _ -> raise Stream.Failure
        and symbol__0029_regexp strm =
          let open Llk_regexps in
          let open PatternBaseToken in
          let rec q0000 lastf ofs =
            let lastf = Some (ofs, 0) in
            match must_peek_nth (ofs + 1) strm with
              Some ("UIDENT", "SEP") -> q0001 lastf (ofs + 1)
            | _ -> lastf
          and q0001 lastf ofs = let lastf = Some (ofs, 1) in lastf in
          q0000 None 0
        and symbol__0030 __strm__ =
          match symbol__0030_matcher __strm__[@llk.first_follow "\",\""] with
            0 ->
              (parser
                 [< '"", ",";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0036 = expr] expected after [','] (in [symbol])"
                        (Grammar.Entry.parse_token_stream expr) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0030_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | _ -> raise Stream.Failure
        and symbol__0031 __strm__ =
          match symbol__0031_matcher __strm__[@llk.first_follow "\",\""] with
            0 ->
              (parser
                 [< '"", ",";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0038 = expr] expected after [','] (in [symbol])"
                        (Grammar.Entry.parse_token_stream expr) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0031_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | _ -> raise Stream.Failure
        and symbol__0032 __strm__ =
          match symbol__0032_matcher __strm__[@llk.first_follow "\",\""] with
            0 ->
              (parser
                 [< '"", ",";
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[y__0040 = expr] expected after [','] (in [symbol])"
                        (Grammar.Entry.parse_token_stream expr) >] ->
                   a)
                __strm__
          | _ -> raise Stream.Failure
        and symbol__0032_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("", ",") -> 0
          | _ -> raise Stream.Failure
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
                        ~msg:"[x__0008 = token__0001] expected after ['$'] (in [token])"
                        token__0001 >] ->
                   a)
                __strm__
          | 2 -> (parser [< '"STRING", x >] -> Special x) __strm__
          | 3 ->
              (parser
                 [< '"UIDENT", x;
                    a =
                      Pa_llk_runtime.Llk_runtime.must_parse
                        ~msg:"[x__0009 = token__0002[<expr>]] expected after [x = UIDENT] (in [token])"
                        (token__0002 x) >] ->
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
        and token__0001 __strm__ =
          match
            token__0001_matcher __strm__[@llk.first_follow "LIDENT | STRING"]
          with
            0 -> (parser [< '"LIDENT", x >] -> Anti x) __strm__
          | 1 ->
              (parser [< '"STRING", x >] -> Anti (Scanf.unescaped x)) __strm__
          | _ -> raise Stream.Failure
        and token__0001_matcher __strm__ =
          match Stream.peek __strm__ with
            Some ("LIDENT", _) -> 0
          | Some ("STRING", _) -> 1
          | _ ->
              raise
                (Stream.Error
                   "[x = LIDENT] or [x = STRING] expected after ['$'] (in [token])")
        and token__0002 x __strm__ =
          match
            token__0002_matcher __strm__[@llk.first_follow "LIDENT | \"[\" | \"(\" | \"_\" | \")\" | UIDENT | \"empty\" | \"eps\" | STRING | \"#\" | \"$\" | \"]\" | \"*\" | \"+\" | \"&\" | \";\" | \"?\" | \"in\" | \"|\" | \"~\" | \"/\""]
          with
            0 ->
              (parser [< '"", "/"; '"STRING", s >] -> Class (x, Some s))
                __strm__
          | 1 -> (parser [< >] -> Class (x, None)) __strm__
          | _ -> raise Stream.Failure
        and token__0002_matcher __strm__ =
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
