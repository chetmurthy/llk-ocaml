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
open Parse_gram ;

module Pr = struct

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value expr = Eprinter.apply_level pr_expr "assign";
value patt = Eprinter.apply pr_patt;
value longident = Eprinter.apply pr_longident;

value comment pc loc = pprintf pc "%s" (Prtools.comm_bef pc.ind loc);
value bar_before elem pc x = pprintf pc "| %p" elem x;
value semi_after elem pc x = pprintf pc "%p;" elem x;
value action expr pc a = expr pc a;

value label pc =
  fun
  [ Some s -> pprintf pc "\"%s\"" s
  | None -> pprintf pc "" ]
;

value assoc pc = fun [
    LEFTA -> pprintf pc "LEFTA"
  | RIGHTA -> pprintf pc "RIGHTA"
  | NONA -> pprintf pc "NONA"
  ]
;

value position pc = fun [
    POS_FIRST -> pprintf pc " FIRST"
  | POS_LAST -> pprintf pc " LAST"
  | POS_BEFORE n -> pprintf pc " BEFORE \"%s\"" n
  | POS_AFTER n -> pprintf pc " AFTER \"%s\"" n
  | POS_LIKE n -> pprintf pc " LIKE \"%s\"" n
  | POS_LEVEL n -> pprintf pc " LEVEL \"%s\"" n
  ]
;

value pair_with s l = List.map (fun g -> (g, s)) l ;

value entry_formals pc l =
  pprintf pc "[%p]" (plist patt 0) (pair_with "," l)
;

value entry_actuals pc l =
  pprintf pc "[%p]" (plist expr 0) (pair_with "," l)
;

value rec string_list pc =
  fun
  [ [s :: sl] -> pprintf pc " \"%s\"%p" s string_list sl
  | [] -> pprintf pc "" ]
;

value pr_option pf pc = fun [
    None -> pprintf pc ""
  | Some x -> pprintf pc "%p" pf x
]
;

value rec rule force_vertic pc { ar_psymbols=sl;  ar_action = a } =
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
                pprintf pc "%p →" (hlistl (semi_after psymbol) psymbol) sl
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
             pprintf pc "@[<2>%p →@;%q@]" (plist psymbol 0) (pair_with ";" sl)
               (action expr) a "|" ])
    | (sl, None) ->
       (match
          horiz_vertic
            (fun () ->
              let s =
                let pc = {(pc) with aft = ""} in
                pprintf pc "%p →" (hlistl (semi_after psymbol) psymbol) sl
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
             pprintf pc "@[<2>%p@]" (plist psymbol 0) (pair_with ";" sl) ])
    ]

and psymbol pc { ap_patt= p; ap_symb = s } =
  match p with
  [ None -> symbol pc s
  | Some p -> pprintf pc "%p =@;%p" pattern p symbol s ]

and pattern pc p =
  match p with
  [ <:patt< $lid:i$ >> -> pprintf pc "%s" i
  | <:patt< _ >> -> pprintf pc "_"
  | <:patt< ($list:pl$) >> ->
      pprintf pc "(%p)" (plist patt 1) (pair_with "," pl)
  | p ->
      pprintf pc "@[<1>(%p)@]" patt p ]

and symbol pc = fun [
      ASlist _ lml symb None ->
       pprintf pc "LIST%s@;%p" (match lml with [ LML_0 -> "0" | LML_1 -> "1" ]) simple_symbol symb
    | ASlist _ lml symb (Some (sep,b)) ->
       pprintf pc "LIST%s@;%p@ @[SEP@;%p%s@]" (match lml with [ LML_0 -> "0" | LML_1 -> "1" ]) 
         simple_symbol symb
         simple_symbol sep
         (if b then " OPT_SEP" else "")

    | ASopt _ sym -> pprintf pc "OPT@;%p" simple_symbol sym

    | ASleft_assoc _ sym1 sym2 e ->
       pprintf pc "LEFT_ASSOC@;%p@;%p WITH %p"
         simple_symbol sym1
         simple_symbol sym2
         expr e

    | ASflag _ sym ->
       pprintf pc "FLAG@;%p" simple_symbol sym

    | ASvala _ sy sl ->
       pprintf pc "V @[<2>%p%p@]" simple_symbol sy string_list sl
    | sy -> simple_symbol pc sy
    ]

and simple_symbol pc sy =
  match sy with
  [ ASregexp _ id ->
    pprintf pc "PREDICT %s" id
  | ASinfer _ n ->
    pprintf pc "INFER %d" n
  | ASnterm _ id args None ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
    pprintf pc "%s%p" id (pr_option entry_actuals) args_opt
  | ASnterm _ id args (Some lev) ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
     pprintf pc "%s%p LEVEL \"%s\"" id (pr_option entry_actuals) args_opt lev
  | ASself _ args ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
     pprintf pc "SELF%p" (pr_option entry_actuals) args_opt
  | ASnext _ args ->
    let args_opt = match args with [ [] -> None | l -> Some l ] in
     pprintf pc "NEXT%p" (pr_option entry_actuals) args_opt
  | ASrules _ rl ->
     horiz_vertic
       (fun () ->
         pprintf pc "[ %p ]"
           (hlist2 (rule False) (bar_before (rule False))) rl.au_rules)
       (fun () ->
         pprintf pc "[ %p ]"
           (vlist2 (rule False) (bar_before (rule False))) rl.au_rules)

  | ASkeyw _ s -> pprintf pc "\"%s\"" s

  | AStok _ cls None -> pprintf pc "%s" cls
  | AStok _ cls (Some constv) -> pprintf pc "%s \"%s\"" cls constv

  | ASlist _ _ _ _ | ASopt _ _ | ASleft_assoc _ _ _ _ | ASflag _ _ | ASvala _ _ _ as sy ->
      pprintf pc "@[<1>(%p)@]" symbol sy
  ]

and entry pc =fun { ae_loc=loc; ae_formals = formals ; ae_name=name; ae_pos=pos ; ae_levels=ll } ->
    let force_vertic =
      if flag_equilibrate_cases.val then
        let has_vertic =
          let f = bar_before (bar_before (rule False)) pc in
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
      pprintf pc "@[<b>%s%p:%p@;[ %p ]@ ;@]" name (pr_option entry_formals) formals_opt (pr_option position) pos 
        (vlist2 (level force_vertic) (bar_before (level force_vertic))) ll      

and level force_vertic pc {al_label = lab; al_assoc=ass; al_rules=rl} =
  let rl = rl.au_rules in
  match (lab, ass) with
  [ (None, None) ->
      if rl = [] then pprintf pc "[ ]"
      else
        pprintf pc "@[<2>[ %p ]@]"
          (vlist2 (rule force_vertic) (bar_before (rule force_vertic))) rl
  | _ ->
      pprintf pc "@[<b>%p@;[ %p ]@]"
        (fun pc ->
           fun
           [ (Some _, None) -> label pc lab
           | (None, Some _) -> (pr_option assoc) pc ass
            | (Some _, Some _) -> pprintf pc "%p %p" label lab (pr_option assoc) ass
            | _ -> assert False ])
        (lab, ass)
        (vlist2 (rule force_vertic) (bar_before (rule force_vertic))) rl ]
  
;

open Llk_regexps ;

value rec pr_regexp_ast pc re = pr_re_let pc re

and pr_re_let pc = fun [
      LETIN _ s re1 re2 -> pprintf pc "let %s = %p@ in %p" s
                             pr_re_disj re1
                             pr_re_disj re2
    | re -> pr_re_disj pc re
    ]

and pr_re_disj pc = fun [
      DISJ _ l -> pprintf pc "@[%p@]" (plist pr_re_conj 2) (pair_with " | " l)
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
      Special _ x -> pprintf pc "\"%s\"" x
    | Class _ x None -> pprintf pc "%s" x
    | Class _ x (Some s) -> pprintf pc "%s/\"%s\"" x s
    | Anti _ x when Llk_regexps.PatternBaseToken.is_lident x -> pprintf pc "$%s" x
    | Anti _ x -> pprintf pc "$\"%s\"" (String.escaped x)
    | Output _ x -> pprintf pc "#%d" x
    | EPS _ -> pprintf pc "eps"
    | ID _ x -> pprintf pc "%s" x
    | x -> pr_re_let pc x
    ]
;

value ident pc id = pprintf pc "%s" id ;

value pr_exports pc l =
  match l with
  [ [] -> pprintf pc ""
  | _ ->
      pprintf pc "EXPORT: %p;@ " (plist ident 2) (pair_with "" l)
  ]
;

value pr_external pc (id, ast) =
  pprintf pc "external %s : PREDICTION %p;" id pr_regexp_ast ast
;

value pr_externals pc l =
    pprintf pc "%p" (plist pr_external 0) (pair_with "" l)
;

value pr_regexp_binding pc (id, ast) =
  pprintf pc "%s = %p;" id pr_regexp_ast ast
;

value pr_regexp_asts pc l =
  match l with
  [ [] -> pprintf pc ""
  | _ ->
      pprintf pc "REGEXPS: %p@ END ;@;" (plist pr_regexp_binding 0) (pair_with "" l)
  ]
;

value longident_lident pc (lio, id) =
  match lio with
  [ None -> pprintf pc "%s" (Pcaml.unvala id)
  | Some li -> pprintf pc "%p.%s" longident (Pcaml.unvala li) (Pcaml.unvala id)
  ]
;
value pr_extend pc = fun [
    None -> pprintf pc ""
  | Some lili -> pprintf pc "EXTEND %p ;" longident_lident lili
]
;

value top pc g =
  pprintf pc "GRAMMAR@;%s:@;@[<b>%p@;%p@;%p@;%p@;%p@]@ END;\n" g.gram_id
    pr_extend g.gram_extend
    pr_exports g.gram_exports
    pr_regexp_asts g.gram_regexp_asts
    pr_externals g.gram_external_asts
    (vlist entry) g.gram_entries
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

end ;
