(* camlp5r *)
(* pa_extend.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open MLast ;
open Pcaml ;
open Pretty;
open Prtools;
open Pa_ppx_base.Pp_MLast ;
open Ord_MLast ;

value equal_expr = Reloc.eq_expr ;
value equal_patt = Reloc.eq_patt ;

value split_ext = ref False;

Pcaml.add_option "-split_ext" (Arg.Set split_ext)
  "Split EXTEND by using functions.";

type loc = Ploc.t [@@deriving (show,eq,ord) ;];

type a_position = [
    POS_LEVEL of string
  | POS_LIKE of string
  | POS_AFTER of string
  | POS_BEFORE of string
  | POS_FIRST | POS_LAST
] [@@deriving (show,eq,ord) ;]
;

type a_assoc = [
    LEFTA
  | RIGHTA
  | NONA
] [@@deriving (show,eq,ord) ;]
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
  | ASleft_assoc of loc and a_symbol and a_symbol and expr
  | ASrules of loc and a_rules
  | ASself of loc
  | AStok of loc and string and option string
  | ASvala of loc and a_symbol and list string
  ]
and lmin_len =
  [ LML_0 | LML_1 ] [@@deriving (show,eq,ord) ;]
;

type _top = (loc * list string * list a_entry) [@@deriving (show,eq,ord) ;] ;

type top = _top ;
value norm_top (loc, gl, el) = (loc, List.sort String.compare gl, List.sort compare_a_entry el) ;
value show_top = show__top ;
value eq_top x y = equal__top (x |> norm_top) (y |> norm_top) ;
value compare_top x y = compare__top (x |> norm_top) (y |> norm_top) ;

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
value top = ( Grammar.Entry.create gram "top" : Grammar.Entry.e top);
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
    [ [ "EXTEND"; /; e = extend_body; "END" ; ";" -> norm_top e ] ]
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
      | UIDENT "LEFT_ASSOC"; s1 = SELF ; s2 = SELF ; UIDENT "WITH" ; e=expr LEVEL "simple" ->
         ASleft_assoc loc s1 s2 e
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

value expr = Eprinter.apply_level pr_expr "simple";
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

(** Reposition entries with [position] markings, to where they belong.

    Entries are either marked with [position]s or not.  Entries'
   levels are either marked with labels or not.  Precisely ONE entry
   SHALL be non-position-marked; all others must be position-marked.

   The levels in entries MAY be labeled but need not be.  All labels
   for an entry will be distinct -- no repeats.

   So take all the entries that are position-marked and extract
   label-sets from them.  TSORT so that an entry with a
   position-marking is AFTER the entry with that label in one of its
   levels.

   Taking the position-marked entry, start inserting from that list of
   tsorted entries.  *)
module Reposition = struct
  open Pa_ppx_utils ;
  open Std ;

  value is_position_marked e = isSome e.ae_pos ;

  value entry_labels e =
    e.ae_levels
    |> List.filter_map (fun [ {al_label=Some l} -> Some l | _ -> None ]) ;

  value entry_position e = e.ae_pos ;

  (** tsort entries by position, label.

      nodes: (entry, position option)
      edges:

        src: node with (e, Some pos)
        dst: node with (e, pos_opt') where e has a level with label [pos]

      edges for LEVEL, LIKE, AFTER, BEFORE, but NOT for FIRST, LAST
   *)

  value entry_name e = e.ae_name ;
  value entry2node e = (entry_name e, entry_position e) ;

  value merge_levels l1 l2 =
    let r1 = l1.al_rules in
    let r2 = l2.al_rules in
    let r1 = {(r1) with au_rules = r1.au_rules @ r2.au_rules} in
    {(l1) with al_rules = r1}
  ;
  value insert1 e0 e1 = do {
    assert (entry_position e0 = None) ;
    if e1.ae_levels = [] then e0 else do {
      match entry_position e1 with [
          None -> assert False
        | Some (POS_LEVEL lev) ->
           let e0_levels =
             e0.ae_levels
             |> List.concat_map (fun l ->
                    if Some lev = l.al_label then
                      [merge_levels l (List.hd e1.ae_levels)] @ (List.tl e1.ae_levels)
                    else [l]
                  ) in
           { (e0) with ae_levels = e0_levels }

        | Some (POS_LIKE _) -> failwith "insert1: LIKE unimplemented"
        | Some (POS_AFTER lev) ->
           let e0_levels =
             e0.ae_levels
             |> List.concat_map (fun l ->
                    if Some lev = l.al_label then [l] @ e1.ae_levels
                    else [l]
                  ) in
           { (e0) with ae_levels = e0_levels }
           
        | Some (POS_BEFORE lev) ->
           let e0_levels =
             e0.ae_levels
             |> List.concat_map (fun l ->
                    if Some lev = l.al_label then e1.ae_levels @ [l]
                    else [l]
                  ) in
           { (e0) with ae_levels = e0_levels }

        | Some POS_FIRST -> { (e0) with ae_levels = e1.ae_levels @ e0.ae_levels }
        | Some POS_LAST ->  { (e0) with ae_levels = e0.ae_levels @ e1.ae_levels }
        ]
    }
  }
  ;
    
  type node = (string * option a_position) ;
  value tsort_nodes (adj : list (node * list node)) =
    let adj = adj |> List.sort_uniq Stdlib.compare in
    Tsort.tsort (fun v l -> [v :: l]) adj [] ;

  value concat_entries = fun [
    [] -> assert False
  | [h::t] as el -> {(h) with ae_levels = List.concat_map (fun e -> e.ae_levels) el }
  ]
  ;

  value coalesce_entries_for ename el =
    let label2node =
      el
      |> List.concat_map (fun e ->
             e
             |> entry_labels
             |> List.map (fun lab -> (lab, entry2node e))
           ) in do {
    if 1 <> List.length (el |> List.map entry_position |> List.find_all ((=) None)) then
      failwith Fmt.(str "construct_graph: exactly one entry named %s MUST be position-free" ename)
    else () ;
    if not (distinct (el |> List.concat_map entry_labels)) then
      failwith Fmt.(str "construct_graph: entry %s does not have distinct labels" ename)
    else () ;

    let adj = el |> List.filter_map (fun e ->
      match entry_position e with [
          Some(POS_LEVEL lev | POS_AFTER lev | POS_BEFORE lev) ->
          (match List.assoc lev label2node with [
               exception Not_found ->
                         failwith Fmt.(str "construct_graph: entry %s, position LEVEL \"%s\" not found"
                                         (entry_name e) lev)
                       | n -> Some (entry2node e, [n])
          ])
        | Some(POS_LIKE levpat) -> failwith Fmt.(str "construct_graph: LIKE position not implemented")
        | Some(POS_FIRST) -> Some (entry2node e, [(entry_name e, None)])
        | Some(POS_LAST) -> Some (entry2node e, [(entry_name e, None)])
        | None -> None
                      ]) in
    let sorted = tsort_nodes adj in
    let sorted_ell =
      sorted
      |> List.map (fun node ->
             el |> List.find_all (fun e -> node = entry2node e)
           ) in
    let sorted_el = List.map concat_entries sorted_ell in
    let (e0, el) = match sorted_el with [
          [] -> assert False
        | [e0::el] when entry_position e0 <> None -> assert False
        | [e0::el] -> (e0, el)
        ] in
    List.fold_left insert1 e0 el
  }
  ;

  value coalesce_entries el =
    let all_entry_names =
      el |> List.map entry_name |> List.sort_uniq String.compare in
    all_entry_names
    |> List.map (fun name ->
      let el = el |> List.find_all (fun e -> name = entry_name e) in
      match el with [
          [({ae_pos = None} as e)] -> e
        | [{ae_pos = Some _}] ->
           failwith Fmt.(str "construct_graph: only one entry named %s, but with position" name)
        | el -> coalesce_entries_for name el
         ])
  ;

  value coalesce (loc, gl, el) = (loc, gl, coalesce_entries el) ;

(*
 exec (loc, gl, el) =
  let project_ename e = (e.ae_name, e) in
  let el = List.map project_ename el in
  let partitions = nway_partition String.equal el in
 *)  
end ;
