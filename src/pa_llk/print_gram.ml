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
open Primtypes ;
open Llk_types ;
open Parse_gram ;

module Pr = struct

type pctxt_t = {
    squote : bool
  ; full : bool
}
;
value normal = { squote = False ; full = True } ;
value errmsg = { squote = True ; full = False } ;

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value expr = Eprinter.apply_level pr_expr "assign";
value patt = Eprinter.apply pr_patt;
value longident = Eprinter.apply pr_longident;

value comment pc loc = pprintf pc "%s" (Prtools.comm_bef pc.ind loc);
value bar_before elem pc x = pprintf pc "| %p" elem x;
value semi_after elem pc x = pprintf pc "%p;" elem x;
value action expr pc a = expr pc a;

value qs pctxt pc s =
    if pctxt.squote then
      pprintf pc "'%s'" s
    else
      pprintf pc "\"%s\"" s
;

value label pctxt pc =
  fun
  [ Some s -> pprintf pc "%p" (qs pctxt) s
  | None -> pprintf pc "" ]
;

value assoc pc = fun [
    LEFTA g -> pprintf pc "%sLEFTA" (if g then "GREEDY " else "NONGREEDY ")
  | RIGHTA -> pprintf pc "RIGHTA"
  | NONA -> pprintf pc "NONA"
  ]
;

value position pctxt pc = fun [
    POS_FIRST -> pprintf pc " FIRST"
  | POS_LAST -> pprintf pc " LAST"
  | POS_BEFORE n -> pprintf pc " BEFORE %p" (qs pctxt) n
  | POS_AFTER n -> pprintf pc " AFTER %p" (qs pctxt) n
  | POS_LIKE n -> pprintf pc " LIKE %p" (qs pctxt) n
  | POS_LEVEL n -> pprintf pc " LEVEL %p" (qs pctxt) n
  ]
;

value pair_with s l = List.map (fun g -> (g, s)) l ;

value entry_formals ~{pctxt=pctxt} pc l =
  let patt = if pctxt.full then patt else (fun pc _ -> pprintf pc "<patt>") in
  pprintf pc "[%p]" (plist patt 0) (pair_with "," l)
;

value entry_actuals ~{pctxt=pctxt} pc l =
  let expr = if pctxt.full then expr else (fun pc _ -> pprintf pc "<expr>") in
  pprintf pc "[%p]" (plist expr 0) (pair_with "," l)
;

value rec string_list pctxt pc = fun [
  [] -> pprintf pc ""
| sl ->
   pprintf pc " %p" (plist (qs pctxt) 0) (pair_with " " sl)
]
;

value pr_option pf pc = fun [
    None -> pprintf pc ""
  | Some x -> pprintf pc "%p" pf x
]
;

value rec rule ~{pctxt} force_vertic pc { ar_psymbols=sl;  ar_action = a } =
  let expr = if pctxt.full then expr else (fun pc _ -> pprintf pc "<expr>") in
  let patt = if pctxt.full then patt else (fun pc _ -> pprintf pc "<patt>") in
  match (sl, a) with [
      ([], None) -> pprintf pc "[ ]"
    | ([], Some a) ->
       pprintf pc "@[<4>→%p %q@]" comment (MLast.loc_of_expr a)
         (action expr) a "|"
    | (sl, Some a) ->
       (match
          horiz_vertic
            (fun () ->
              let s =
                let pc = {(pc) with aft = ""} in
                pprintf pc "%p →" (hlistl (semi_after (psymbol ~{pctxt=pctxt})) (psymbol ~{pctxt=pctxt})) sl
              in
              Some s)
            (fun () -> None)
        with
          [ Some s1 ->
            let pc = {(pc) with bef = ""} in
            horiz_vertic
              (fun () ->
                if force_vertic then sprintf "\n"
                else pprintf pc "%s %q" s1 (action expr) a "|")
              (fun () ->
                pprintf pc "%s@;<1 4>%q" s1 (action expr) a "|")
          | None ->
             pprintf pc "@[<2>%p →@;%q@]" (plist (psymbol ~{pctxt=pctxt}) 0) (pair_with ";" sl)
               (action expr) a "|" ])
    | (sl, None) ->
       (match
          horiz_vertic
            (fun () ->
              let s =
                let pc = {(pc) with aft = ""} in
                pprintf pc "%p" (hlistl (semi_after (psymbol ~{pctxt=pctxt})) (psymbol ~{pctxt=pctxt})) sl
              in
              Some s)
            (fun () -> None)
        with
          [ Some s1 ->
            let pc = {(pc) with bef = ""} in
            horiz_vertic
              (fun () ->
                if force_vertic then sprintf "\n"
                else pprintf pc "%s" s1)
              (fun () ->
                pprintf pc "%s" s1)
          | None ->
             pprintf pc "@[<2>%p@]" (plist (psymbol ~{pctxt=pctxt}) 0) (pair_with ";" sl) ])
    ]

and rule_psymbols~{pctxt} pc sl =
  pprintf pc "%p" (hlistl (semi_after (psymbol ~{pctxt=pctxt})) (psymbol ~{pctxt=pctxt})) sl

and psymbol ~{pctxt} pc { ap_patt= p; ap_symb = s } =
  match p with
  [ None -> symbol ~{pctxt=pctxt} pc s
  | Some p -> pprintf pc "%p =@;%p" (pattern ~{pctxt=pctxt}) p (symbol ~{pctxt=pctxt}) s ]

and pattern ~{pctxt} pc p =
  let patt = if pctxt.full then patt else (fun pc _ -> pprintf pc "<patt>") in
  match p with
  [ <:patt< $lid:i$ >> -> pprintf pc "%s" i
  | <:patt< _ >> -> pprintf pc "_"
  | <:patt< ($list:pl$) >> ->
      pprintf pc "(%p)" (plist patt 1) (pair_with "," pl)
  | p ->
      pprintf pc "@[<1>(%p)@]" patt p ]

and symbol ~{pctxt} pc =
  let expr = if pctxt.full then expr else (fun pc _ -> pprintf pc "<expr>") in
  fun [
      ASlist _ g lml symb None ->
       pprintf pc "%sLIST%s@;%p"
         (if g then "GREEDY " else "NONGREEDY ")
         (match lml with [ LML_0 -> "0" | LML_1 -> "1" ]) (simple_symbol ~{pctxt=pctxt}) symb
    | ASlist _ g lml symb (Some (sep,b)) ->
       pprintf pc "%sLIST%s@;%p@ @[SEP@;%p%s@]"
         (if g then "GREEDY " else "NONGREEDY ")
         (match lml with [ LML_0 -> "0" | LML_1 -> "1" ]) 
         (simple_symbol ~{pctxt=pctxt}) symb
         (simple_symbol ~{pctxt=pctxt}) sep
         (if b then " OPT_SEP" else "")

    | ASopt _ g sym -> pprintf pc "%sOPT@;%p" 
         (if g then "GREEDY " else "NONGREEDY ")
         (simple_symbol ~{pctxt=pctxt}) sym

    | ASoptv _ g e sym -> pprintf pc "%sOPTV@;%p@;%p" 
         (if g then "GREEDY " else "NONGREEDY ")
         expr e
         (simple_symbol ~{pctxt=pctxt}) sym

    | ASleft_assoc _ g sym1 sym2 e ->
       pprintf pc "%sLEFT_ASSOC@;%p@;ACCUMULATE %p WITH %p"
         (if g then "GREEDY " else "NONGREEDY ")
         (simple_symbol ~{pctxt=pctxt}) sym1
         (simple_symbol ~{pctxt=pctxt}) sym2
         expr e

    | ASflag _ g sym ->
       pprintf pc "%sFLAG@;%p"
         (if g then "GREEDY " else "NONGREEDY ")
         (simple_symbol ~{pctxt=pctxt}) sym

    | ASvala _ sy sl ->
       pprintf pc "V @[<2>%p%p@]"
         (simple_symbol ~{pctxt=pctxt}) sy (string_list pctxt) sl
    | sy -> (simple_symbol ~{pctxt=pctxt}) pc sy
    ]

and simple_symbol ~{pctxt} pc sy =
  match sy with
  [ ASpriority _ n ->
    pprintf pc "PRIORITY %d" n
  | ASnterm _ id args None ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
    pprintf pc "%s%p" (Name.print id) (pr_option (entry_actuals ~{pctxt=pctxt})) args_opt
  | ASnterm _ id args (Some lev) ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
     pprintf pc "%s%p LEVEL %p"
       (Name.print id)
       (pr_option (entry_actuals ~{pctxt=pctxt})) args_opt
       (qs pctxt) lev
  | ASself _ args ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
     pprintf pc "SELF%p" (pr_option (entry_actuals ~{pctxt=pctxt})) args_opt
  | ASnext _ args ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
     pprintf pc "NEXT%p" (pr_option (entry_actuals ~{pctxt=pctxt})) args_opt
  | ASrules _ rl ->
     horiz_vertic
       (fun () ->
         pprintf pc "[ %p ]"
           (hlist2 (rule ~{pctxt=pctxt} False) (bar_before (rule ~{pctxt=pctxt} False))) rl.au_rules)
       (fun () ->
         pprintf pc "[ %p ]"
           (vlist2 (rule ~{pctxt=pctxt} False) (bar_before (rule ~{pctxt=pctxt} False))) rl.au_rules)

  | ASkeyw _ s -> qs pctxt pc s
  | AStok _ cls None -> pprintf pc "%s" cls
  | AStok _ cls (Some constv) ->
       pprintf pc "%s %p" cls (qs pctxt) constv

  | ASsyntactic _ sym ->
       pprintf pc "(%p)?" (symbol ~{pctxt=pctxt}) sym

  | ASanti _ sl ->
     pprintf pc "ANTI @[<2>%p@]" (string_list pctxt) sl

  | ASlist _ _ _ _ _ | ASopt _ _ _ | ASoptv _ _ _ _ | ASleft_assoc _ _ _ _ _ | ASflag _ _ _ | ASvala _ _ _ as sy ->
      pprintf pc "@[<1>(%p)@]" (symbol ~{pctxt=pctxt}) sy
  ]

and preceding_psymbols ~{pctxt} pc = fun [
      [] -> pprintf pc ""
    | psl ->
       pprintf pc "(* PRECEDING: [%p] *)@;" (plist (psymbol ~{pctxt=pctxt}) 0) (pair_with "; " psl)
    ]      
and source_symbol ~{pctxt} pc = fun [
      None -> pprintf pc ""
    | Some s ->
       pprintf pc "(* SOURCE: [%p] *)@;" (symbol ~{pctxt=pctxt}) s
    ]      

and entry ~{pctxt} pc =fun { ae_loc=loc; ae_formals = formals ; ae_name=name; ae_pos=pos ; ae_levels=ll
                             ; ae_preceding_psymbols = preceding_psl
                             ; ae_source_symbol = ss
                           } ->
    let force_vertic =
      if flag_equilibrate_cases.val then
        let has_vertic =
          let f = bar_before (bar_before (rule ~{pctxt=pctxt} False)) pc in
          List.exists
            (fun lev ->
              List.exists
                (fun (r : a_rule) ->
                  horiz_vertic
                    (fun () ->
                      let _ : string = f r in
                      False)
                    (fun () -> True))
                lev.al_rules.au_rules)
            ll
        in
        has_vertic
      else False
    in
    let formals_opt = match formals with [ [] -> None | l -> Some l ] in
    comm_bef pc.ind loc ^
      pprintf pc "@[<b>%s%p:%p@;%p@;%p[ %p ]@ ;@]"
        (Name.print name)
        (pr_option (entry_formals ~{pctxt=pctxt})) formals_opt
        (preceding_psymbols ~{pctxt=pctxt}) preceding_psl
        (source_symbol ~{pctxt=pctxt}) ss
        (pr_option (position pctxt)) pos 
        (vlist2 (level ~{pctxt=pctxt} force_vertic) (bar_before (level ~{pctxt=pctxt} force_vertic))) ll      

and level ~{pctxt=pctxt} force_vertic pc {al_label = lab; al_assoc=ass; al_rules=rl} =
  let rl = rl.au_rules in
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then pprintf pc "[ ]"
      else
        pprintf pc "@[<2>[ %p ]@]"
          (vlist2 (rule ~{pctxt=pctxt} force_vertic) (bar_before (rule ~{pctxt=pctxt} force_vertic))) rl
  | _ ->
      pprintf pc "@[<b>%p@;[ %p ]@]"
        (fun pc ->
           fun
           [ (Some _, None) -> label pctxt pc lab
           | (None, Some _) -> (pr_option assoc) pc ass
            | (Some _, Some _) -> pprintf pc "%p %p" (label pctxt) lab (pr_option assoc) ass
            | _ -> assert False ])
        (lab, ass)
        (vlist2 (rule ~{pctxt=pctxt} force_vertic) (bar_before (rule ~{pctxt=pctxt} force_vertic))) rl ]
  
;

open Llk_regexps ;

value rec pr_regexp_ast pc re = pr_re_let pc re

and pr_re_let pc = fun [
      LETIN _ s re1 re2 -> pprintf pc "let %s = %p@ in %p" (Name.print s)
                             pr_re_disj re1
                             pr_re_disj re2
    | re -> pr_re_disj pc re
    ]

and pr_re_disj pc = fun [
      DISJ _ [] -> pprintf pc "empty"
    | DISJ _ l -> pprintf pc "@[%p@]" (plist pr_re_conj 2) (pair_with " | " l)
    | re -> pr_re_conj pc re
    ]

and pr_re_conj pc = fun [
      CONJ _ l -> pprintf pc "@[%p@]" (plist pr_re_conc 2) (pair_with "  & " l)
    | re -> pr_re_conc pc re
    ]

and pr_re_conc pc = fun [
      CONC _ l -> pprintf pc "@[%p@]" (plist pr_re_neg 2) (pair_with " " l)
    | re -> pr_re_neg pc re
    ]

and pr_re_neg pc = fun [
      NEG _ re -> pprintf pc "~ %p" pr_re_opt re
    | re -> pr_re_opt pc re
    ]

and pr_re_opt pc = fun [
      OPT _ re -> pprintf pc "%p ?" pr_re_star re
    | re -> pr_re_star pc re
    ]

and pr_re_star pc = fun [
      STAR _ re -> pprintf pc "%p *" pr_re_simple re
    | re -> pr_re_simple pc re
    ]

and pr_re_simple pc = fun [
      TOKEN _ t -> pprintf pc "%p" pr_tokenast t
    | EPS _ -> pprintf pc "eps"
    | ANY _ -> pprintf pc "_"
    | EXCEPT _ l -> pprintf pc "[^ %p]" (plist pr_tokenast 0) (pair_with " " l)
    | ID _ x -> pprintf pc "%s" (Name.print x)
    | x -> pr_re_let pc x
    ]
and pr_tokenast pc = fun [
      Special x -> pprintf pc "\"%s\"" x
    | Class x None -> pprintf pc "%s" x
    | Class x (Some s) -> pprintf pc "%s/\"%s\"" x s
    | Anti x when Llk_regexps.PatternBaseToken.is_lident x -> pprintf pc "$%s" x
    | Anti x -> pprintf pc "$\"%s\"" (String.escaped x)
    | Output x -> pprintf pc "#%d" x
    ]
;

value ident pc id = pprintf pc "%s" id ;
value name pc id = pprintf pc "%s" (Name.print id) ;

value pr_exports pc l =
  match l with
  [ [] -> pprintf pc ""
  | _ ->
      pprintf pc "EXPORT: %p;@ " (plist name 2) (pair_with "" l)
  ]
;

value pr_external pc (id, ast) =
  pprintf pc "external %s : PREDICTION %p;" (Name.print id) pr_regexp_ast ast
;

value pr_externals pc l =
    pprintf pc "%p" (plist pr_external 0) (pair_with "" l)
;

value pr_regexp_binding pc (id, ast) =
  pprintf pc "%s = %p;" (Name.print id) pr_regexp_ast ast
;

value pr_regexp_asts pc l =
  match l with
  [ [] -> pprintf pc ""
  | _ ->
      pprintf pc "REGEXPS: %p@ END ;@;" (plist pr_regexp_binding 0) (pair_with "" l)
  ]
;

value longident_lident pctxt pc (lio, id) =
  let longident = if pctxt.full then longident else (fun pc _ -> pprintf pc "<longident>") in
  match lio with
  [ None -> pprintf pc "%s" (Pcaml.unvala id)
  | Some li -> pprintf pc "%p.%s" longident (Pcaml.unvala li) (Pcaml.unvala id)
  ]
;
value pr_extend ~{pctxt} pc = fun [
    None -> pprintf pc ""
  | Some lili -> pprintf pc "EXTEND %p ;" (longident_lident pctxt) lili
]
;

value top ?{pctxt=normal} pc g =
  pprintf pc "GRAMMAR@;%s:@;@[<b>%p@;%p@;%p@;%p@;%p@]@ END;\n" g.gram_id
    (pr_extend ~{pctxt=pctxt}) g.gram_extend
    pr_exports g.gram_exports
    pr_regexp_asts g.gram_regexp_asts
    pr_externals g.gram_external_asts
    (vlist (entry ~{pctxt=pctxt})) g.gram_entries
;

end ;


module RT = struct

  value pa loc s = 
  let g = s |> Stream.of_string |> Grammar.Entry.parse Pa.top in
  { (g) with gram_loc = loc }
  ;

  value pr x = 
    x |> Pr.top Pprintf.empty_pc |> print_string ;

  value string s = s |> pa Ploc.dummy |> pr ;

  value read_file name =
    name |> Fpath.v |> Bos.OS.File.read |> Rresult.R.get_ok ;

 value pa_regexp_ast s =
 s |> Stream.of_string |> Grammar.Entry.parse Pa.regexp ;

  value pr_regexp_ast x = 
    x |> Pr.pr_regexp_ast Pprintf.empty_pc |> print_string ;

 value pa_regexp s =
 s |> Stream.of_string |> Grammar.Entry.parse Pa.regexp |> Llk_regexps.normalize_astre [] ;
end ;
