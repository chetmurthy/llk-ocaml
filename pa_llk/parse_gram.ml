(* camlp5r *)
(* pa_extend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open MLast ;
open Pcaml ;
open Pretty;
open Prtools;
open Pa_ppx_base ;
open Pp_MLast ;
open Ord_MLast ;
open Llk_types ;

module Pa = struct

open Llk_regexps ;
module Compiled(R : sig value rawcheck :  Stream.t (string * string) -> option int ;
                        value name : string ;
                 end) = struct
  value rawcheck = R.rawcheck ;
  value pred strm = match rawcheck strm with [ None -> False | Some _ -> True ] ;
  value check_f strm = if pred strm then () else raise Stream.Failure ;
  value check_not_f strm = if not(pred strm) then () else raise Stream.Failure ;
  value check = Grammar.Entry.of_parser Pcaml.gram ("check_"^R.name) check_f ;
  value check_not = Grammar.Entry.of_parser Pcaml.gram ("check_not_"^R.name) check_not_f ;
end
;


open Pcaml;
value top = ( Grammar.Entry.create gram "top" : Grammar.Entry.e top);
value grammar_body = Grammar.Entry.create gram "grammar_body";
value symbol = Grammar.Entry.create gram "symbol";
value rule = Grammar.Entry.create gram "rule";
value rule_list = Grammar.Entry.create gram "rule_list";
value level_list = Grammar.Entry.create gram "level_list";
value level = Grammar.Entry.create gram "level";
value symbol = Grammar.Entry.create gram "symbol";

EXTEND
  GLOBAL:
    expr
    top grammar_body symbol rule rule_list level level_list symbol
  ;
  top:
    [ [ "GRAMMAR"; e = grammar_body; "END" ; ";" ; EOI -> norm_top e ] ]
  ;
  grammar_body:
    [ [ gid = UIDENT ; ":" ;
        sl = [ l = global -> l | -> [] ];
        rl = [ l = regexps -> l | -> [] ];
        el = LIST1 [ e = entry; ";" -> e ] ->
          {gram_loc=loc; gram_id=gid; gram_globals=sl; gram_regexp_asts=rl; gram_regexps=[]; gram_entries=el} ] ]
  ;
  global:
    [ [ UIDENT "GLOBAL"; ":"; sl = LIST1 LIDENT; ";" -> sl ] ]
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
    [ [ p = LIDENT; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s}
      | i = LIDENT; 
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
          {ap_loc = loc; ap_patt = None; ap_symb = ASnterm loc i args lev}
      | p = pattern; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some p; ap_symb = s}
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
         ASlist loc LML_0 s sep
      | UIDENT "LIST1"; s = SELF; sep = OPT sep_opt_sep ->
         ASlist loc LML_1 s sep
      | UIDENT "OPT"; s = SELF ->
         ASopt loc s
      | UIDENT "LEFT_ASSOC"; s1 = SELF ; s2 = SELF ; UIDENT "WITH" ; e=expr LEVEL "simple" ->
         ASleft_assoc loc s1 s2 e
      | UIDENT "FLAG"; s = SELF ->
          ASflag loc s ]
    | "vala"
      [ UIDENT "V"; UIDENT "SELF";
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        al = LIST0 STRING ->
          let s = ASself loc args in
          ASvala loc s al
      | UIDENT "V"; UIDENT "NEXT";
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        al = LIST0 STRING ->
          let s = ASnext loc args in
          ASvala loc s al
      | UIDENT "V"; x = UIDENT; al = LIST0 STRING ->
          let s = AStok loc x None in
          ASvala loc s al
      | UIDENT "V"; s = NEXT; al = LIST0 STRING ->
          ASvala loc s al ]
    | "simple"
      [ UIDENT "SELF" ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ->
          ASself loc args
      | UIDENT "NEXT" ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ]  ->
          ASnext loc args
      | "["; rl = LIST0 rule SEP "|"; "]" ->
          ASrules loc {au_loc = loc; au_rules = rl}
      | x = UIDENT ->
          AStok loc x None
      | x = UIDENT; e = STRING ->
          AStok loc x (Some e)
      | e = STRING ->
          ASkeyw loc e

      | id = LIDENT ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
        ASnterm loc id args lev

      | "("; s_t = SELF; ")" -> s_t ] ]
  ;
  pattern:
    [ [ i = LIDENT -> <:patt< $lid:i$ >>
      | "_" -> <:patt< _ >>
      | "("; p = SELF; ")" -> <:patt< $p$ >>
      | "("; p = SELF; ","; pl = patterns_comma; ")" ->
          <:patt< ( $list:[p :: pl]$ ) >> ] ]
  ;
  patterns_comma:
    [ [ pl = SELF; ","; p = pattern -> pl @ [p] ]
    | [ p = pattern -> [p] ] ]
  ;

  regexp_entry: [ [ n = LIDENT ; "=" ; r = regexp ; ";" -> (n,r) ] ] ;

  regexp: [ [ x = e6 -> x ] ] ;

  e6: [ [ "let" ; s=LIDENT ; "=" ; re1 = e5 ; "in" ; re2 = e5 -> LETIN loc s re1 re2
        | x = e5 -> x
        ] ] ;

  e5: [ [ l = LIST1 e4 SEP "|" -> DISJ loc l ] ] ;

  e4: [ [ l = LIST1 e3 SEP "&" -> CONJ loc l ] ] ;

  e3: [ [ l = LIST1 e2 -> CONC loc l ] ] ;

  e2: [ [ "~"; x = e1 -> NEG loc x | x = e1 -> x ] ] ;

  e1: [ [ x = e0; "*" -> STAR loc x | x = e0 -> x ] ] ;

  e0:
    [ [ x = STRING -> Special loc x
      | x = UIDENT -> Class loc x
      | "$" ; x = LIDENT -> Anti loc x
      | "("; x = e6; ")" -> x
      | "eps" -> EPS loc
      | x = LIDENT -> ID loc x
      ]
    ]
  ;

END;

end ;
