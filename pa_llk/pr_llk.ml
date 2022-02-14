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
open Pa_llk ;

module Pr = struct

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value expr = Eprinter.apply_level pr_expr "assign";
value patt = Eprinter.apply pr_patt;

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

value entry_formals pc l =
  let l = List.map (fun id -> (id, ",")) l in
  pprintf pc "[%p]" (plist patt 0) l
;

value entry_actuals pc l =
  let l = List.map (fun id -> (id, ",")) l in
  pprintf pc "[%p]" (plist expr 0) l
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
             let sl = List.map (fun s -> (s, ";")) sl in
             pprintf pc "@[<2>%p →@;%q@]" (plist psymbol 0) sl
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
             let sl = List.map (fun s -> (s, ";")) sl in
             pprintf pc "@[<2>%p@]" (plist psymbol 0) sl ])
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
      let pl = List.map (fun p -> (p, ",")) pl in
      pprintf pc "(%p)" (plist patt 1) pl
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
  [ ASnterm _ id args None ->
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

value ident pc id = pprintf pc "%s" id ;

value extend_body pc (globals, entries) =
  match globals with
  [ [] -> vlist entry pc entries
  | _ ->
      let globals = List.map (fun g -> (g, "")) globals in
      pprintf pc "@[<b>GLOBAL: %p;@ %p@]" (plist ident 2) globals
        (vlist entry) entries ]
;

value top pc (_, sl, el) =
  pprintf pc "EXTEND@;%p@ END" extend_body (sl,el) ;

end ;


module RT = struct

  value pa s = 
  s |> Stream.of_string |> Grammar.Entry.parse Pa.top ;

  value pr x = 
    x |> Pr.top Pprintf.empty_pc |> print_string ;

  value string s = s |> pa |> pr ;

  value with_file f name =
    let s = name |> Fpath.v |> Bos.OS.File.read |> Rresult.R.get_ok in
    f s ;

  value file fn = with_file string fn ;
end ;
