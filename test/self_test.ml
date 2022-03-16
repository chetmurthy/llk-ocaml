
open Pcaml ;;

open Llk_types ;;
open Llk_regexps ;;

let expr_LEVEL_simple = expr ;;

[@@@llk
{foo|
GRAMMAR LLKGram:
EXPORT: expr
    top grammar_body symbol rule rule_list level level_list symbol regexp;

REGEXPS:
  check_lident_equal = LIDENT "=" ;
  check_lident_lbracket = LIDENT "[" ;
  check_pattern_equal = "(" ("(" | LIDENT | "_" | "," | ")")* "=" ;
END;

external expr : PREDICTION LIDENT ;
external expr_LEVEL_simple : PREDICTION LIDENT ;
external patt : PREDICTION LIDENT ;

  top:
    [ [ "GRAMMAR"; e = grammar_body; "END" ; ";" ; EOI -> norm_top e ] ]
  ;
  grammar_body:
    [ [ gid = UIDENT ; ":" ;
        expl = [ l = exports -> l | -> [] ];
        rl = [ l = regexps -> l | -> [] ];
        extl = [ l = externals -> l | -> [] ];
        el = LIST1 [ e = entry; ";" -> e ] ->
          { gram_loc=loc
          ; gram_id=gid
          ; gram_exports=expl
          ; gram_external_asts=extl
          ; gram_regexp_asts=rl
          ; gram_entries=el
    } ] ]
  ;
  exports:
    [ [ UIDENT "EXPORT"; ":"; sl = LIST1 LIDENT; ";" -> sl ] ]
  ;
  externals:
    [ [ l = LIST1 external_entry -> l ] ]
  ;
  external_entry:
    [ [ "external"; s = LIDENT; ":"; UIDENT "PREDICTION" ; r = regexp ; ";" -> (s,r) ] ]
  ;
  regexps:
    [ [ UIDENT "REGEXPS"; ":"; rl = LIST1 regexp_entry; "END" ; ";" -> rl ] ]
  ;
  entry:
    [ [ n = LIDENT;
        formals = [ "[" ; l = LIST1 patt SEP "," ; "]" -> l | -> [] ] ;
        ":"; pos = OPT position; ll = level_list ->
          {ae_loc = loc; ae_formals = formals ; ae_name = n; ae_pos = pos; ae_levels = ll}
      ] ]
  ;
  position:
    [ [ UIDENT "FIRST" -> POS_FIRST
      | UIDENT "LAST" -> POS_LAST
      | UIDENT "BEFORE"; n = STRING -> POS_BEFORE n
      | UIDENT "AFTER"; n = STRING -> POS_AFTER n
      | UIDENT "LIKE"; n = STRING -> POS_LIKE n
      | UIDENT "LEVEL"; n = STRING -> POS_LEVEL n ] ]
  ;
  level_list:
    [ [ "["; ll = LIST0 level SEP "|"; "]" -> ll ] ]
  ;
  level:
    [ [ lab = OPT STRING; ass = OPT assoc; rules = rule_list ->
          {al_loc = loc; al_label = lab; al_assoc = ass; al_rules = rules} ] ]
  ;
  assoc:
    [ [ UIDENT "LEFTA" -> LEFTA
      | UIDENT "RIGHTA" -> RIGHTA
      | UIDENT "NONA" -> NONA ] ]
  ;
  rule_list:
    [ [ "["; "]" -> {au_loc = loc; au_rules = []}
      | "["; rules = LIST1 rule SEP "|"; "]" ->
          {au_loc = loc; au_rules = rules} ] ]
  ;
  rule:
    [ [ psl = LIST0 psymbol SEP ";"; "->"; act = expr ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = Some act}
      | psl = LIST0 psymbol SEP ";" ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = None} ] ]
  ;
  psymbol:
    [ [ check_lident_equal; p = LIDENT; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s}
      | check_lident_lbracket; p = LIDENT; 
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
          {ap_loc = loc; ap_patt = None; ap_symb = ASnterm (loc, p, args, lev)}
      | check_pattern_equal ; p = paren_pattern; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some p; ap_symb = s}
       | "_" ; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< _ >>; ap_symb = s}
      | s = symbol ->
          {ap_loc = loc; ap_patt = None; ap_symb = s} ] ]
  ;
  sep_opt_sep:
    [ [ sep = UIDENT "SEP"; t = symbol; b = FLAG [ UIDENT "OPT_SEP" ] ->
          (t, b) ] ]
  ;
  symbol:
    [ "top" NONA
      [ UIDENT "LIST0"; s = SELF; sep = OPT sep_opt_sep ->
         ASlist (loc, LML_0, s, sep)
      | UIDENT "LIST1"; s = SELF; sep = OPT sep_opt_sep ->
         ASlist (loc, LML_1, s, sep)
      | UIDENT "OPT"; s = SELF ->
         ASopt (loc, s)
      | UIDENT "LEFT_ASSOC"; s1 = SELF ; UIDENT "ACCUMULATE" ; s2 = SELF ; UIDENT "WITH" ; e=expr_LEVEL_simple ->
         ASleft_assoc (loc, s1, s2, e)
      | UIDENT "FLAG"; s = SELF ->
          ASflag (loc, s)
      | s = NEXT -> s
      ]
    | "vala"
      [ UIDENT "V"; s = NEXT; al = LIST0 STRING ->
          ASvala (loc, s, al)
      | s = NEXT -> s
      ]
    | "simple"
      [ UIDENT "SELF" ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ->
          ASself (loc, args)
      | UIDENT "NEXT" ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ]  ->
          ASnext (loc, args)
      | "["; rl = LIST0 rule SEP "|"; "]" ->
          ASrules (loc, {au_loc = loc; au_rules = rl})
      | x = UIDENT ->
          AStok (loc, x, None)
      | x = UIDENT; "/"; e = STRING ->
          AStok (loc, x, Some e)
      | e = STRING ->
          ASkeyw (loc, e)

      | id = LIDENT ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
        ASnterm (loc, id, args, lev)

      | UIDENT "PREDICT" ; id = LIDENT ->
        ASregexp (loc, id)

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

  regexp_entry: [ [ n = LIDENT ; "=" ; r = regexp ; ";" -> (n,r) ] ] ;

  regexp: [ [ x = e6 -> x ] ] ;

  e6: [ [ "let" ; s=LIDENT ; "=" ; re1 = e5 ; "in" ; re2 = e5 -> LETIN (loc, s, re1, re2)
        | x = e5 -> x
        ] ] ;

  e5: [ [ l = LIST1 e4 SEP "|" -> DISJ (loc, l) ] ] ;

  e4: [ [ l = LIST1 e3 SEP "&" -> CONJ (loc, l) ] ] ;

  e3: [ [ l = LIST1 e2 -> CONC (loc, l) ] ] ;

  e2: [ [ "~"; x = e2' -> NEG (loc, x) | x = e2' -> x ] ] ;
 
  e2': [ [ x = e1 ; "?" -> OPT (loc, x) | x = e1 -> x ] ] ;

  e1: [ [ x = e0; "*" -> STAR (loc, x) | x = e0 -> x ] ] ;

  e0:
    [ [ x = STRING -> Special(loc, x)
      | x = UIDENT -> Class(loc, x, None)
      | x = UIDENT ; "/" ; s = STRING -> Class(loc, x, Some s)
      | "$" ; x = LIDENT -> Anti(loc, x)
      | "#" ; x = INT -> Output(loc, int_of_string x)
      | "("; x = e6; ")" -> x
      | "eps" -> EPS loc
      | x = LIDENT -> ID(loc, x)
      ]
    ]
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
