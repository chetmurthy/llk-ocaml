
open Pcaml ;;

open Primtypes ;;
open Llk_types ;;
open Llk_regexps ;;
open Parse_gram ;;
open Print_gram ;;

let expr_LEVEL_simple = expr ;;

[@@@llk
{foo|
GRAMMAR LLKGram:
EXTEND Pcaml.gram ;
EXPORT: bootstrapped_top;

REGEXPS:
  check_lident_equal = LIDENT "=" ;
  check_lident_lbracket = LIDENT "[" ;
  check_pattern_equal = "(" ("(" | LIDENT | "_" | "," | ")")* "=" ;
END;

external expr : PREDICTION LIDENT ;
external expr_LEVEL_simple : PREDICTION LIDENT ;
external patt : PREDICTION LIDENT ;
external longident_lident : PREDICTION UIDENT | LIDENT | $uid | $_uid | $lid | $_lid ;

  bootstrapped_top:
    [ [ "GRAMMAR"; e = grammar_body; "END" ; ";" ; EOI -> norm_top e ] ]
  ;
  grammar_body:
    [ [ gid = UIDENT ; ":" ;
        extend_opt = OPT [ UIDENT/"EXTEND" ; id = longident_lident ; ";" -> id ] ;
        expl = [ l = exports -> l | -> [] ];
        rl = [ l = regexps -> l | -> [] ];
        extl = [ l = externals -> l | -> [] ];
        el = LIST1 [ e = entry; ";" -> e ] ->
          { gram_loc=loc
          ; gram_extend = extend_opt
          ; gram_id=gid
          ; gram_exports=expl
          ; gram_external_asts=extl
          ; gram_regexp_asts=Llk_types.default_regexps @ rl
          ; gram_entries=el
    } ] ]
  ;
  exports:
    [ [ UIDENT/"EXPORT"; ":"; sl = LIST1 LIDENT; ";" -> List.map Name.mk sl ] ]
  ;
  externals:
    [ [ l = LIST1 external_entry -> l ] ]
  ;
  external_entry:
    [ [ "external"; s = LIDENT; ":"; UIDENT/"PREDICTION" ; r = regexp ; ";" -> (Name.mk s,r) ] ]
  ;
  regexps:
    [ [ UIDENT/"REGEXPS"; ":"; rl = LIST1 regexp_entry; "END" ; ";" -> rl ] ]
  ;
  entry:
    [ [ n = LIDENT;
        formals = [ "[" ; l = LIST1 patt SEP "," ; "]" -> l | -> [] ] ;
        ":"; pos = OPT position; ll = level_list ->
          {ae_loc = loc
          ; ae_formals = formals
          ; ae_name = Name.mk n
          ; ae_pos = pos
          ; ae_levels = ll
          ; ae_preceding_psymbols = []
          }
      ] ]
  ;
  position:
    [ [ UIDENT/"FIRST" -> POS_FIRST
      | UIDENT/"LAST" -> POS_LAST
      | UIDENT/"BEFORE"; n = STRING -> POS_BEFORE n
      | UIDENT/"AFTER"; n = STRING -> POS_AFTER n
      | UIDENT/"LIKE"; n = STRING -> POS_LIKE n
      | UIDENT/"LEVEL"; n = STRING -> POS_LEVEL n ] ]
  ;
  level_list:
    [ [ "["; ll = LIST0 level SEP "|"; "]" -> ll ] ]
  ;
  level:
    [ [ lab = OPT STRING; ass = OPT assoc; rules = rule_list ->
          {al_loc = loc; al_label = lab; al_assoc = ass; al_rules = rules} ] ]
  ;
  assoc:
    [ [ UIDENT/"LEFTA" -> LEFTA
      | UIDENT/"RIGHTA" -> RIGHTA
      | UIDENT/"NONA" -> NONA ] ]
  ;
  rule_list:
    [ [ "["; "]" -> {au_loc = loc; au_rules = []}
      | "["; rules = LIST1 rule SEP "|"; "]" ->
          {au_loc = loc; au_rules = rules} ] ]
  ;
  rule:
    [ [ psl = LIST1 psymbol SEP ";"; "->"; act = expr ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = Some act}
      | "->"; act = expr ->
          {ar_loc = loc; ar_psymbols = []; ar_action = Some act}
      | psl = LIST1 psymbol SEP ";" ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = None}
      ] ]
  ;
  psymbol:
    [ [ check_lident_equal; p = LIDENT; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s}
      | check_lident_lbracket; p = LIDENT; 
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT/"LEVEL"; s = STRING -> s ] ->
          {ap_loc = loc; ap_patt = None; ap_symb = ASnterm (loc, Name.mk p, args, lev)}
      | check_pattern_equal ; p = paren_pattern; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some p; ap_symb = s}
       | "_" ; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< _ >>; ap_symb = s}
      | s = symbol ->
          {ap_loc = loc; ap_patt = None; ap_symb = s} ] ]
  ;
  sep_opt_sep:
    [ [ sep = UIDENT/"SEP"; t = symbol; b = FLAG [ UIDENT/"OPT_SEP" ] ->
          (t, b) ] ]
  ;
  symbol:
    [ "top" NONA
      [ g = FLAG UIDENT/"GREEDY" ; UIDENT/"LIST0"; s = SELF; sep = OPT sep_opt_sep ->
         ASlist (loc, g, LML_0, s, sep)
      | g = FLAG UIDENT/"GREEDY" ; UIDENT/"LIST1"; s = SELF; sep = OPT sep_opt_sep ->
         ASlist (loc, g, LML_1, s, sep)
      | UIDENT/"OPT"; s = SELF ->
         ASopt (loc, s)
      | UIDENT/"LEFT_ASSOC"; s1 = SELF ; UIDENT/"ACCUMULATE" ; s2 = SELF ; UIDENT/"WITH" ; e=expr_LEVEL_simple ->
         ASleft_assoc (loc, s1, s2, e)
      | UIDENT/"FLAG"; s = SELF ->
          ASflag (loc, s)
      | s = NEXT -> s
      ]
    | "vala"
      [ UIDENT/"V"; s = NEXT; al = LIST0 STRING ->
          ASvala (loc, s, al)
      | s = NEXT -> s
      ]
    | "simple"
      [ UIDENT/"SELF" ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ->
          ASself (loc, args)
      | UIDENT/"NEXT" ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ]  ->
          ASnext (loc, args)
      | "["; rl = LIST0 rule SEP "|"; "]" ->
          ASrules (loc, {au_loc = loc; au_rules = rl})
      | x = UIDENT ->
          AStok (loc, x, None)
      | x = UIDENT; "/"; e = STRING ->
          AStok (loc, x, Some (Scanf.unescaped e))
      | e = STRING ->
          ASkeyw (loc, e)

      | id = LIDENT ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT/"LEVEL"; s = STRING -> s ] ->
        ASnterm (loc, Name.mk id, args, lev)

      | UIDENT/"PREDICT" ; id = LIDENT ->
        ASregexp (loc, Name.mk id)

      | "("; s_t = SELF; ")" -> s_t ] ]
  ;
  pattern:
    [ [ i = LIDENT -> <:patt< $lid:i$ >>
      | "_" -> <:patt< _ >>
      | p = paren_pattern -> p
      ] ]
  ;
  paren_pattern:
    [ [ "("; l = LIST1 pattern SEP "," ; ")" ->
          <:patt< ( $list:l$ ) >> ] ]
  ;

  regexp_entry: [ [ n = LIDENT ; "=" ; r = regexp ; ";" -> (Name.mk n,r) ] ] ;

  regexp: [ [ x = e6 -> x ] ] ;

  e6: [ [ "let" ; s=LIDENT ; "=" ; re1 = e5 ; "in" ; re2 = e6 -> LETIN (loc, Name.mk s, re1, re2)
        | x = e5 -> x
        ] ] ;

  e5: [ [ l = LIST1 e4 SEP "|" -> DISJ (loc, l) ] ] ;

  e4: [ [ l = LIST1 e3 SEP "&" -> CONJ (loc, l) ] ] ;

  e3: [ [ l = LIST1 e2 -> CONC (loc, l) ] ] ;

  e2: [ [ "~"; x = e2' -> NEG (loc, x) | x = e2' -> x ] ] ;
 
  e2': [ [ x = e1 ; "?" -> OPT (loc, x) | x = e1 -> x ] ] ;

  e1: [ [ x = e0; "*" -> STAR (loc, x) | x = e0 -> x ] ] ;

  e0:
    [ [ t = token -> TOKEN (loc, t)
      | "("; x = e6; ")" -> x
      | "eps" -> EPS loc
      | "empty" -> DISJ(loc, [])
      | "_" -> ANY loc
      | x = LIDENT -> ID(loc, Name.mk x)
      ]
    ]
  ;
  token: [ [
      x = STRING -> Special x
    | x = UIDENT -> Class (x, None)
    | x = UIDENT ; "/" ; s = STRING -> Class (x, Some s)
    | "$" ; x = LIDENT -> Anti x
    | "$" ; x = STRING -> Anti (Scanf.unescaped x)
    | "#" ; x = INT -> Output (int_of_string x)
    ] ]
  ;


END ;
|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let loc = Ploc.dummy
let tests = "simple" >::: [
      "LLKGram" >:: (fun _ ->
        let txt = {| e: [ [ "a" -> () ] ] |} in
(*
        assert_equal ~cmp:equal_a_entry (pa Pa.entry txt) (pa LLKGram.entry txt)
 *)
()
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
