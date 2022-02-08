(* camlp5r *)
(* pa_extend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open MLast ;
open Pcaml ;
open Pretty;
open Prtools;
open Pa_ppx_base.Pp_MLast ;

value equal_expr = Reloc.eq_expr ;
value equal_patt = Reloc.eq_patt ;

value split_ext = ref False;

Pcaml.add_option "-split_ext" (Arg.Set split_ext)
  "Split EXTEND by using functions.";

type loc = Ploc.t [@@deriving (show,eq) ;];

type a_position = [
    POS_LEVEL of string
  | POS_LIKE of string
  | POS_AFTER of string
  | POS_BEFORE of string
  | POS_FIRST | POS_LAST
] [@@deriving (show,eq) ;]
;

type a_assoc = [
    LEFTA
  | RIGHTA
  | NONA
] [@@deriving (show,eq) ;]
;

type a_entry =
  { ae_loc : loc;
    ae_name : string;
    ae_pos : option a_position;
    ae_levels : list a_level }
and a_level =
  { al_loc : loc;
    al_label : option string;
    al_assoc : option a_assoc;
    al_rules : a_rules }
and a_rules =
  { au_loc : loc;
    au_rules : list a_rule }
and a_rule =
  { ar_loc : loc;
    ar_psymbols : list a_psymbol;
    ar_action : option expr }
and a_psymbol =
  { ap_loc : loc;
    ap_patt : option patt;
    ap_symb : a_symbol }
and a_symbol =
  [ ASflag of loc and a_symbol
  | ASkeyw of loc and string
  | ASlist of loc and lmin_len and a_symbol and
      option (a_symbol * bool)
  | ASnext of loc
  | ASnterm of loc and string and option string
  | ASopt of loc and a_symbol
  | ASrules of loc and a_rules
  | ASself of loc
  | AStok of loc and string and option string
  | ASvala of loc and a_symbol and list string
  ]
and lmin_len =
  [ LML_0 | LML_1 ] [@@deriving (show,eq) ;]
;

module Pa = struct

open Token_regexps ;
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
value top = Grammar.Entry.create gram "top";
value extend_body = Grammar.Entry.create gram "extend_body";
value symbol = Grammar.Entry.create gram "symbol";
value rule = Grammar.Entry.create gram "rule";
value rule_list = Grammar.Entry.create gram "rule_list";
value level_list = Grammar.Entry.create gram "level_list";
value level = Grammar.Entry.create gram "level";
value semi_sep = Grammar.Entry.of_parser gram "';'" (parser [: `("", ";") :] -> ()) ;

EXTEND
  GLOBAL:
    expr
    top extend_body symbol rule rule_list level level_list
  ;
  top:
    [ [ "EXTEND"; /; e = extend_body; "END" ; ";" -> e ] ]
  ;
  extend_body:
    [ [ sl = [ l = global -> l | -> [] ];
        el = LIST1 [ e = entry; semi_sep -> e ] ->
          (loc, sl, el) ] ]
  ;
  global:
    [ [ UIDENT "GLOBAL"; ":"; sl = LIST1 LIDENT; semi_sep -> sl ] ]
  ;
  entry:
    [ [ n = LIDENT; ":"; pos = OPT position; ll = level_list ->
          {ae_loc = loc; ae_name = n; ae_pos = pos; ae_levels = ll} ] ]
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
    [ [ psl = LIST0 psymbol SEP semi_sep; "->"; act = expr ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = Some act}
      | psl = LIST0 psymbol SEP semi_sep ->
          {ar_loc = loc; ar_psymbols = psl; ar_action = None} ] ]
  ;
  psymbol:
    [ [ p = LIDENT; "="; s = symbol ->
          {ap_loc = loc; ap_patt = Some <:patt< $lid:p$ >>; ap_symb = s}
      | i = LIDENT; lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
          {ap_loc = loc; ap_patt = None; ap_symb = ASnterm loc i lev}
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
      | UIDENT "FLAG"; s = SELF ->
          ASflag loc s ]
    | "vala"
      [ UIDENT "V"; UIDENT "SELF"; al = LIST0 STRING ->
          let s = ASself loc in
          ASvala loc s al
      | UIDENT "V"; UIDENT "NEXT"; al = LIST0 STRING ->
          let s = ASnext loc in
          ASvala loc s al
      | UIDENT "V"; x = UIDENT; al = LIST0 STRING ->
          let s = AStok loc x None in
          ASvala loc s al
      | UIDENT "V"; s = NEXT; al = LIST0 STRING ->
          ASvala loc s al ]
    | "simple"
      [ UIDENT "SELF" ->
          ASself loc
      | UIDENT "NEXT" ->
          ASnext loc
      | "["; rl = LIST0 rule SEP "|"; "]" ->
          ASrules loc {au_loc = loc; au_rules = rl}
      | x = UIDENT ->
          AStok loc x None
      | x = UIDENT; e = STRING ->
          AStok loc x (Some e)
      | e = STRING ->
          ASkeyw loc e

      | id = LIDENT ;
        lev = OPT [ UIDENT "LEVEL"; s = STRING -> s ] ->
        ASnterm loc id lev

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
END;

end ;

module Pr = struct

value flag_equilibrate_cases = Pcaml.flag_equilibrate_cases;

value expr = Eprinter.apply pr_expr;
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
    POS_FIRST -> pprintf pc "FIRST"
  | POS_LAST -> pprintf pc "LAST"
  | POS_BEFORE n -> pprintf pc "BEFORE \"%s\"" n
  | POS_AFTER n -> pprintf pc "AFTER \"%s\"" n
  | POS_LIKE n -> pprintf pc "LIKE \"%s\"" n
  | POS_LEVEL n -> pprintf pc "LEVEL \"%s\"" n
  ]
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

    | ASflag _ sym ->
       pprintf pc "FLAG@;%p" simple_symbol sym

    | ASvala _ sy sl ->
       pprintf pc "V @[<2>%p%p@]" simple_symbol sy string_list sl
    | sy -> simple_symbol pc sy
    ]

and simple_symbol pc sy =
  match sy with
  [ ASnterm _ id None -> pprintf pc "%s" id
  | ASnterm _ id (Some lev) -> pprintf pc "%s LEVEL \"%s\"" id lev
  | ASself _ -> pprintf pc "SELF"
  | ASnext _ -> pprintf pc "NEXT"
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

  | ASlist _ _ _ _ | ASopt _ _ | ASflag _ _ | ASvala _ _ _ as sy ->
      pprintf pc "@[<1>(%p)@]" symbol sy
  ]

and entry pc =fun { ae_loc=loc; ae_name=name; ae_pos=pos ; ae_levels=ll } ->
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
    comm_bef pc.ind loc ^
      pprintf pc "@[<b>%s:%p@;[ %p ]@ ;@]" name (pr_option position) pos 
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
  value string s = 
  s |> Stream.of_string |> Grammar.Entry.parse Pa.top |> Pr.top Pprintf.empty_pc |> print_string ;

  value file fn =
    let s = fn |> Fpath.v |> Bos.OS.File.read |> Rresult.R.get_ok in
    string s ;
end ;
