
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
EXPORT: bootstrapped_top entry level_list level rule_list rule symbol psymbol;

external expr : PREDICTION LIDENT | INT | QUOTATION | "(" | "[" | "{" ;
external expr_LEVEL_simple : PREDICTION LIDENT | INT | QUOTATION | "(" | "[" | "{" ;
external patt : PREDICTION LIDENT | INT | QUOTATION | "(" | "[" | "{" ;
external longident_lident : PREDICTION UIDENT | LIDENT | $uid | $_uid | $lid | $_lid ;

  bootstrapped_top:
    [ [ "GRAMMAR"; e = grammar_body; "END" ; ";" ; EOI -> norm_top e ] ]
  ;
  grammar_body:
    [ [ gid = UIDENT ; ":" ;
        extend_opt = OPT [ "EXTEND" ; id = longident_lident ; ";" -> id ] ;
        expl = [ l = exports -> l | -> [] ];
        rl = [ l = regexps -> l | -> [] ];
        extl = [ l = externals -> l | -> [] ];
        el = LIST1 [ e = entry; ";" -> e ] ->
          { gram_loc=loc
          ; gram_extend = extend_opt
          ; gram_id=gid
          ; gram_exports=expl
          ; gram_external_asts=extl
          ; gram_regexp_asts=rl
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
          ; ae_source_symbol = None
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
    [ [ lab = NONGREEDY OPT STRING; ass = NONGREEDY OPT assoc; rules = rule_list ->
          {al_loc = loc; al_label = lab; al_assoc = ass; al_rules = rules} ] ]
  ;
  assoc:
    [ [ g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"LEFTA" -> LEFTA g
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
    [ [ p = LIDENT; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s}
      | ([paren_pattern; "="])? ; p = paren_pattern; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some p; ap_symb = s}
       | "_" ; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< _ >>; ap_symb = s}
      | s = symbol ->
          {ap_loc = loc; ap_patt = None; ap_symb = s} ] ]
  ;
  sep_opt_sep:
    [ [ sep = UIDENT/"SEP"; t = symbol; b = GREEDY FLAG [ UIDENT/"OPT_SEP" ] ->
          (t, b) ] ]
  ;
  symbol:
    [ "top" NONA
      [ g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"LIST0"; s = NEXT; sep = GREEDY OPT sep_opt_sep ->
         ASlist (loc, g, LML_0, s, sep)
      | g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"LIST1"; s = NEXT; sep = GREEDY OPT sep_opt_sep ->
         ASlist (loc, g, LML_1, s, sep)
      | g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"OPT"; s = NEXT ->
         ASopt (loc, g, s)
      | g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"OPTV"; e = expr; s = NEXT ->
         ASoptv (loc, g, e, s)
      | g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"LEFT_ASSOC"; s1 = NEXT ; UIDENT/"ACCUMULATE" ; s2 = NEXT ; UIDENT/"WITH" ; e=expr_LEVEL_simple ->
         ASleft_assoc (loc, g, s1, s2, e)
      | g = [ UIDENT/"GREEDY" -> true | UIDENT/"NONGREEDY" -> false | -> true ] ; UIDENT/"FLAG"; s = NEXT ->
          ASflag (loc, g, s)
      | s = NEXT -> s
      ]
    | "vala"
      [ UIDENT/"V"; s = SELF; al = GREEDY LIST0 STRING ->
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

      | UIDENT/"ANTI" ; l = GREEDY LIST1 STRING -> ASanti(loc, l)

      | id = LIDENT ;
        args = [ "[" ; l = LIST1 expr SEP "," ; "]" -> l | -> [] ] ;
        lev = OPT [ UIDENT/"LEVEL"; s = STRING -> s ] ->
        ASnterm (loc, Name.mk id, args, lev)

      | UIDENT/"PRIORITY" ; n = signed_int ->
        ASpriority (loc, n)

      | "!!" -> ASmutation_barrier loc

      | "("; s_t = NEXT; ")" -> s_t
      | "{"; e = expr; "}" ; "?" -> ASsemantic(loc, e)
      | "("; s_t = NEXT; ")" ; "?" -> ASsyntactic (loc, s_t)
      ] ]
  ;
  signed_int: [ [ n = INT -> int_of_string n | "-" ; n = INT -> -(int_of_string n) ] ] ;
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

  e1: [ [ x = e0; "*" -> STAR (loc, x)
        | x = e0; "+" -> CONC(loc, [x; STAR (loc, x)])
        | x = e0 -> x ] ] ;

  e0:
    [ [ t = token -> TOKEN (loc, t)
      | "("; x = e6; ")" -> x
      | "eps" -> EPS loc
      | "empty" -> DISJ(loc, [])
      | "_" -> ANY loc
      | "[" ; "^"; l = LIST1 token ; "]" -> EXCEPT (loc, l)
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

let pa loc s =
  let g = s |> Stream.of_string |> Grammar.Entry.parse LLKGram.bootstrapped_top in
  {(g) with gram_loc = loc}
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
