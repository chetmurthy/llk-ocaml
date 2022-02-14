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
open Pa_ppx_utils ;
open Ppxutil ;

open Llk_types ;
open Pr_llk ;


(** Verify lexical hygiene of grammars.

    1. The lexical environment of a symbol is always the
   pattern-bindings of the symbols to its left, or in outer rules, to
   the left, and then including the formals of the entry containing
   that symbol.

    2. That lexical environment MUST contain only distinct identifiers
   in patterns.
 *)
module CheckLexical = struct

value vars_of_patt p =
  let rec vrec = fun [
        <:patt< $lid:x$ >> -> [x]
      | <:patt< ( $list:l$ ) >> -> List.concat_map vrec l
      | _ -> []
      ] in
  vrec p
;

module Env = struct
  type t = list string ;
  value mk l = l ;
  value addl l1 l2 = l1@l2 ;
  value mem x l = List.mem x l ;
end ;

value rec check_symbol env = fun [
      ASflag _ s -> check_symbol env s
  | ASkeyw _ _ -> ()
  | ASlist _ _ s None -> check_symbol env s
  | ASlist _ _ s (Some (s2, _)) -> do { check_symbol env s ; check_symbol env s2 }

  | ASnext _ _ -> ()
  | ASnterm _ _ _ _ -> ()
  | ASopt _ s -> check_symbol env s
  | ASleft_assoc _ s1 s2 _ ->  do { check_symbol env s1 ; check_symbol env s2 }
  | ASrules _ rs -> check_rules env rs
  | ASself _ _ -> ()
  | AStok _ _ _ -> ()
  | ASvala _ s _ -> check_symbol env s
]

and check_rule env r =
  List.fold_left (fun env ps ->
      let patvars = match ps.ap_patt with [ None -> [] | Some p -> vars_of_patt p ] in do {
          patvars |> List.iter (fun v ->
            if Env.mem v env then
              raise_failwithf ps.ap_loc "CheckLexical.check_rule: lexical hygiene violation on var %s" v
            else ()
          ) ;
          let env = Env.addl patvars env in
          check_symbol env ps.ap_symb ;
          env
      }
    ) env r.ar_psymbols

and check_rules env rl = List.iter (fun r -> ignore (check_rule env r)) rl.au_rules
;

value check_level env l = check_rules env l.al_rules ;

value check_levels env ll = List.iter (check_level env) ll ;

value check_entry e =
  check_levels (e.ae_formals |> List.concat_map vars_of_patt |> Env.mk) e.ae_levels ;

value exec ((_, _, el) as x) = do { List.iter check_entry el ; x } ;

end ;

(** Coalesce entries with [position] markings, to where they belong.

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
module S1Coalesce = struct
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

  value exec (loc, gl, el) = (loc, gl, coalesce_entries el) ;

end ;

module CheckNoPosition = struct

value exec ((_, _, el) as x) = do {
  el |> List.iter (fun e ->
      if e.ae_pos <> None then
        raise_failwithf e.ae_loc "CheckNoPosition: entry %s still has a position" e.ae_name
      else ()
    ) ;
  x
}
;

end ;

(** convert entry [e]with multiple levels into multiple entries [e__%04d],

    An entry with N multiple levels

    e: [ {LEFTA,RIGHTA,NONA} [ ... ] [ ... ] .... ] ;

    specifies precedence and associativity, and needs to be broken up into
    N+2 entries.

    LEFTA levels need to be replaced with the LEFT_ASSOC complex symbol,
    recursive calls replaced.

    RIGHTA levels need to have their recursive calls replaced, EXCEPT
    for right-recursion.

    NONA levels need to have ALL recursive calls replaced

    default associativity is ALWAYS NONA, and a level that doesn't actually
    have any left/right recursion, can still be NONA.

    The return value is a pair:

      a dictionary of rewrites of [e] and all its named levels, to new entry-names,
      a list of new entries with those rewrites already applied.

 *)

module Subst = struct

type key_t = [ NT of string and option string | NEXT | SELF ] ;

value lookup_rho s rho : string = List.assoc s rho ;

value make_dt rho =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm loc id args sopt as s ->
        (match lookup_rho (NT id sopt) rho with [
             id' -> ASnterm loc id' args None
           | exception Not_found -> s
        ])
      
      | ASself loc args as s ->
         (match lookup_rho SELF rho with [
            id' -> ASnterm loc id' args None
          | exception Not_found -> s
          ])
      
      | ASnext loc args as s ->
         (match lookup_rho NEXT rho with [
            id' -> ASnterm loc id' args None
          | exception Not_found -> s
          ])

      | s -> fallback_migrate_a_symbol dt s
      ] in
  { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol }
;

value entry rho ps =
  let dt = make_dt rho in
  dt.migrate_a_entry dt ps
;

value psymbol rho ps =
  let dt = make_dt rho in
  dt.migrate_a_psymbol dt ps
;

value symbol rho ps =
  let dt = make_dt rho in
  dt.migrate_a_symbol dt ps
;

value rule rho ps =
  let dt = make_dt rho in
  dt.migrate_a_rule dt ps
;

value rules rho rl = List.map (rule rho) rl ;

end ;

value rec formals2actuals l = List.map f2a l
and f2a = fun [
      <:patt:< $lid:id$ >> -> <:expr< $lid:id$ >>
    | <:patt:< ( $list:l$ ) >> -> <:expr< ( $list:formals2actuals l$ ) >>
    | <:patt:< ( $p$ : $t$ ) >> -> <:expr< ( $f2a p$ : $t$ ) >>
    | <:patt:< () >> -> <:expr< () >>
    | p ->
       raise_failwithf (loc_of_patt p) "formals2actuals: malformed formal"
    ]
;

module S2Precedence = struct 

value rewrite_righta loc (ename,eformals) ~{cur} ~{next} rho rl =
  let right_rho = Subst.[
        (SELF, cur)
       ;(NT ename None, cur)
    ] in
  let rl =
    rl
    |> List.map (fun r ->
           let psl = r.ar_psymbols in
           let (last, psl) = Std.sep_last psl in
           let psl = List.map (Subst.psymbol rho) psl in
           let last = Subst.psymbol right_rho last in
           let psl = psl @ [last] in
           {(r) with ar_psymbols = psl}
         ) in
  let last_rule = {ar_loc = loc;
                   ar_psymbols = [{ap_loc = loc;
                                   ap_patt = Some <:patt< x >> ;
                                   ap_symb = ASnterm loc next (formals2actuals eformals) None}];
                   ar_action = Some <:expr< x >> } in
  rl @ [last_rule]
;

value rewrite_lefta loc ename ~{cur} ~{next} rho rl =
  let left_rho = Subst.[
      (SELF, next)
     ;(NT ename None, next)
    ] in
  let left_symbol = (List.hd (List.hd rl).ar_psymbols).ap_symb in
  let right_rl =
    rl
  |> List.map (fun r ->
         let left_patt = (List.hd r.ar_psymbols).ap_patt in
         let left_patt = match left_patt with [ None -> <:patt< _ >> | Some p -> p ] in
         {(r) with ar_psymbols = List.tl r.ar_psymbols ;
                   ar_action = r.ar_action |> Option.map (fun act -> <:expr< fun [ $left_patt$ -> $act$ ] >>)
         }) in
  let right_rl = Subst.rules rho right_rl in
  let left_symbol = Subst.symbol left_rho left_symbol in
  let left_assoc_symbol =
    ASleft_assoc loc left_symbol
      (ASrules loc {au_loc=loc; au_rules = right_rl})
      <:expr< fun x f -> f x >> in
  [{ ar_loc=loc
   ; ar_psymbols=[{ ap_loc=loc
                  ; ap_patt = Some <:patt< __x__ >>
                  ; ap_symb = left_assoc_symbol}]
   ; ar_action = Some <:expr< __x__ >> }]
;

  (** rewrite a level into a entry that eschews associativity and
     label markings, instead doing it explicitly.

      (default) NONA: SELF, NEXT, and calls to the entry itself, are
     all rewritten to [next].

      RIGHTA: check that the LAST psymbol in each rule of the level is
     either SELF or the entry itself.  Then rewrite non-right-hand
     SELF/NEXT/entry calls to [next] and the right-hand SELF/entry
     calls to [cur]

     LEFTA: check that the FIRST psymbol in each rule of the level is
     either SELF or the entry itself.  Check that all FIRST psymbols
     are equal.  Then:

     (1) remove the first psymbol from each rule
     (2) rewrite all SELF/NEXT/entry calls to [next]
     (3) turn this into a [rules]
     (4) and then produce the levels:

     [cur] : [ [ x = LEFT_ASSOC [ [next] ] [rules] WITH (fun f x -> x f) -> x ] ] ;

   *)

value rewrite1 e (ename, eargs) ~{cur} ~{next} dict l = do {
    if ([] = l.al_rules.au_rules) then
      raise_failwithf l.al_rules.au_loc "rewrite1: entry %s has an empty level" ename
    else () ;
    let loc = l.al_loc in
    let l = match l.al_assoc with [
          None | Some NONA ->
            let rules =
              l.al_rules.au_rules
              |> Subst.rules Subst.[
                     (SELF, next)
                    ;(NEXT, next)
                    ;(NT ename None, next)
                   ] in
            {
              (l) with
              al_label = None ;
              al_assoc = None ;
              al_rules = {(l.al_rules) with au_rules = rules}
            }

          | Some RIGHTA ->
             let rl = l.al_rules.au_rules in do {
             if rl |> List.exists (fun r -> List.length r.ar_psymbols < 2) then
               raise_failwithf l.al_rules.au_loc "rewrite1: entry %s RIGHTA level rules must all have at least 2 psymbols"
                 ename
             else () ;
             let last_symbol = 
               let (last_psymbol, _) = Std.sep_last (List.hd rl).ar_psymbols in
               last_psymbol.ap_symb in
             if not (rl |> List.for_all (fun r -> 
                               equal_a_symbol last_symbol (fst (Std.sep_last r.ar_psymbols)).ap_symb)) then
               raise_failwithf l.al_rules.au_loc "rewrite1: entry %s RIGHTA level does not have identical last symbols"
                 ename
             else () ;
             match last_symbol with [
                 ASnterm _ name _ None when name = ename -> ()
               | ASself _ _ -> ()
               | _ -> failwith Fmt.(str "rewrite1: entry %s RIGHTA level has last psymbol non-recursive"
                                      ename)
               ] ;
             let rl = rewrite_righta loc (ename,eargs) ~{cur=cur} ~{next=next} Subst.[
                          (NEXT, next)
                         ;(SELF, next)
                         ;(NT ename None, next)
                        ] rl in
             {
               (l) with
               al_label = None ;
               al_assoc = None ;
               al_rules = {(l.al_rules) with au_rules = rl}
             }
          }

          | Some LEFTA ->
             let rl = l.al_rules.au_rules in do {
             if rl |> List.exists (fun r -> List.length r.ar_psymbols < 2) then
               raise_failwithf l.al_rules.au_loc "rewrite1: entry %s LEFTA level rules must all have at least 2 psymbols"
                 ename
             else () ;
             let first_symbol =
               let first_psymbol = List.hd (List.hd rl).ar_psymbols in
               first_psymbol.ap_symb in
             rl |> List.iter (fun r ->
                       if not (equal_a_symbol first_symbol (List.hd r.ar_psymbols).ap_symb) then
                         raise_failwithf r.ar_loc "rewrite1: entry %s LEFTA level does not have identical first symbols"
                           ename
                       else ()
                     ) ;
             match first_symbol with [
                 ASnterm _ name _ None when name = ename -> ()
               | ASself _ _ -> ()
               | _ -> raise_failwithf l.al_rules.au_loc "rewrite1: entry %s LEFTA level has first psymbol non-recursive"
                        ename
               ] ;
             let rl = rewrite_lefta loc ename ~{cur=cur} ~{next=next} Subst.[
                          (NEXT, next)
                         ;(SELF, next)
                         ;(NT ename None, next)
                        ] rl in
             {
               (l) with
               al_label = None ;
               al_assoc = None ;
               al_rules = {(l.al_rules) with au_rules = rl}
             }
          }

        ] in
    {(e) with ae_name = cur ; ae_levels = [l]}
}
;

value new_name e n = Printf.sprintf "%s__%04d" e.ae_name n ;

value passthru_entry e fromi toj =
  let from_name = match fromi with [ None -> e.ae_name | Some i -> new_name e i ] in
  let to_name = new_name e toj in
  let loc = e.ae_loc in
  let formals = e.ae_formals in
  let actuals = formals2actuals e.ae_formals in
  {ae_loc = loc; ae_name = from_name; ae_formals = formals ; ae_pos = None;
   ae_levels =
     [{al_loc = loc; al_label = None; al_assoc = None;
       al_rules =
         {au_loc = loc;
          au_rules =
            [{ar_loc = loc;
              ar_psymbols = [{ap_loc = loc;
                              ap_patt = Some <:patt< x >> ;
                              ap_symb = ASnterm loc to_name actuals None}];
              ar_action =
                Some <:expr< x >>}]}}]}
;

(** to convert a multilevel entry (of N levels) to multiple entries
    we create entries:

    e: [ [ x = e__0 -> x ] ] ;
    e__0: [ [ x = e__1 -> x ] ] ;
    e__1 ...
    ....
    e__n ...
    e__{n+1}: [ [ x = e__0 -> x ] ] ;

    So this means we create 3 new entries to surround our
    N entry-for-each-level.

 *)


value exec1 e = do {
  assert (e.ae_pos = None) ;
  let ename = e.ae_name in
  let formals = e.ae_formals in
  let levels = e.ae_levels in
  let n_levels = List.length levels in
  let named_levels =
    List.mapi (fun i l -> (i+1, new_name e (i+1), l)) levels in
  let dict =
    named_levels
    |> List.filter_map (fun (i, newname, l) ->
           match l.al_label with [
               None -> None
             | Some _ as lab -> Some (Subst.NT ename lab, newname)
         ]) in
  let newents =
    named_levels
    |> List.map (fun (i, newname, l) ->
           rewrite1 e (ename,formals) ~{cur=newname} ~{next=new_name e (i+1)} dict l) in
  let top2_entries = [
      passthru_entry e None 0 ;
      passthru_entry e (Some 0) 1
    ] in
  let bottom_entries = [
      passthru_entry e (Some (n_levels+1)) 0
    ] in

  (dict, top2_entries @ newents @ bottom_entries)
}
;

value substitute_self e =
  Subst.entry Subst.[(SELF, e.ae_name)] e
;

value exec0 e =
  if List.length e.ae_levels <=1 then ([], [substitute_self e])
  else exec1 e ;

value exec (loc, gl, el) =
  let pl = List.map exec0 el in
  let dict = pl |> List.concat_map fst in
  let el = List.concat_map snd pl in
  let el = List.map (Subst.entry dict) el in
  (loc, gl, el)
;

end ;

module CheckNoLabelAssocLevel = struct

value check_no_level el =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm loc nt _ (Some _) ->
        raise_failwithf loc "CheckNoLabelAssocLevel: level marking found on nonterminal %s" nt
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol } in
  List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) el
;

value exec ((_, _, el) as x) = do {
  check_no_level el ;
  el |> List.iter (fun e ->
    e.ae_levels |> List.iter (fun l -> do {
      match l.al_label with [
          None -> ()
        | Some lab ->
           raise_failwithf e.ae_loc "CheckNoLabelAssocLevel: entry %s still has a label %s" e.ae_name lab
        ] ;
      match l.al_assoc with [
          None -> ()
        | Some a ->
           raise_failwithf e.ae_loc "CheckNoLabelAssocLevel: entry %s still has an assoc %a" e.ae_name pp_a_assoc a
        ]
    })
  ) ;
  x
}
;

end ;

module S4LeftFactorize = struct

value extract_left_factors1 rl =
  if List.length rl > 1 &&
       rl |> List.for_all (fun r -> List.length r.ar_psymbols > 0) &&
         (let left_psymbol = List.hd (List.hd rl).ar_psymbols in
          rl |> List.for_all (fun r -> equal_a_psymbol left_psymbol (List.hd r.ar_psymbols))) then
    let left_psymbol = List.hd (List.hd rl).ar_psymbols in
    ([left_psymbol],
     rl |> List.map (fun r -> {(r) with ar_psymbols = List.tl r.ar_psymbols }))

  else ([], rl)
;

value rec extract_left_factors rl =
  match extract_left_factors1 rl with [
      ([], rl) -> ([], rl)
    | (l, rl) ->
       let (l', rl) = extract_left_factors rl in
       (l @ l', rl)
    ]
;

value left_factorize0 loc rl =
  match extract_left_factors rl with [
      ([], rl) -> rl
    | (factors,rl) ->
       let right_psymb = {
           ap_loc = loc
         ; ap_patt = Some <:patt< __x__ >>
         ; ap_symb = ASrules loc { au_loc = loc ; au_rules = rl }
         } in
       [{ ar_loc = loc
        ; ar_psymbols = factors @ [ right_psymb ]
        ; ar_action = Some <:expr< __x__ >> }]
    ]
;

value left_factorize loc rl =
  let mt_rules = List.filter (fun r -> [] = r.ar_psymbols) rl in
  let nonmt_rules = List.filter (fun r -> [] <> r.ar_psymbols) rl in
  let head_psymbols = List.map (fun r -> List.hd r.ar_psymbols) nonmt_rules in
  let head_psymbols = List.sort_uniq compare_a_psymbol head_psymbols in
  let partitions =
    head_psymbols
    |> List.map (fun ps ->
           nonmt_rules |> List.filter (fun r -> equal_a_psymbol ps (List.hd r.ar_psymbols))) in
  List.concat ((List.map (left_factorize0 loc) partitions) @ [mt_rules])
;

value make_dt () =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_level = dt.migrate_a_level in
  let migrate_a_level dt l = 
    let l = fallback_migrate_a_level dt l in
    let loc = l.al_loc in    
    {(l) with al_rules = {(l.al_rules) with au_rules = left_factorize loc l.al_rules.au_rules } }
  in
  { (dt) with Llk_migrate.migrate_a_level = migrate_a_level }
;

value left_factorize_level l =
  let dt = make_dt () in
  dt.migrate_a_level dt l
;

value left_factorize_levels l = do {
  assert (1 = List.length l) ;
  List.map left_factorize_level l
}
;

value exec0 e = {(e) with ae_levels = left_factorize_levels e.ae_levels } ;

value exec (loc, gl, el) = (loc, gl, List.map exec0 el) ;

end ;

type token = Token_regexps.PatternBaseToken.t == [ CLS of string | SPCL of string ]
;

module type TOKENSET = sig
  type t 'a = 'b ;
  value mt : t 'a ;
  value mk : list 'a -> t 'a ;
  value add : t 'a -> 'a -> t 'a ;
  value addl : t 'a -> list 'a -> t 'a ;
  value mem : 'a -> t 'a -> bool ;
  value export : t 'a -> list 'a ;
  value union : t 'a -> t 'a -> t 'a ;
  value disjoint : t 'a -> t 'a -> bool ;
  value unionl : list (t 'a) -> t 'a ;
  value except : 'a -> t 'a -> t 'a ;
  value map : ('a -> 'b) -> t 'a -> t 'b ;
end ;

module TokenSet : TOKENSET = struct
  type t 'a = list 'a ;
  value mt = [] ;
  value canon l = List.sort_uniq Stdlib.compare l ;
  value add l x = [x::l] |> canon ;
  value addl l l2 = l@l2 |> canon ;
  value mk l = l |> canon ;
  value mem x l = List.mem x l ;
  value export l = l ;
  value union = addl ;
  value unionl l = l |> List.concat |> canon ;
  value disjoint a b = [] = Std.intersect a b ;
  value except x l = Std.except x l ;
  value map f l = List.map f l |> canon ;
end ;
module TS = TokenSet ;

module type SETMAP = sig
  type t 'a = 'c;
  type set_t 'a = 'd ;
  value canon : t 'a -> t 'a ;
  value mt : t 'a ;
  value add : t 'a -> (string * 'a) -> t 'a ;
  value lookup : string -> t 'a -> set_t 'a ;
  value addset : t 'a -> (string * set_t 'a) -> t 'a ;
  value export : t 'a -> list (string * list 'a) ;
end ;

module SetMap : (SETMAP with type set_t 'a = TS.t 'a) = struct
  type set_t 'a = TS.t 'a ;
  type t 'a = list (string * set_t 'a) ;

  value canon m = m |> List.sort Stdlib.compare ;
  value mt = [] ;
  value addset m (nt, ts') =
    match List.assoc nt m with [
        ts ->
        let m = List.remove_assoc nt m in
        canon [(nt,TS.union ts ts') :: m]

      | exception Not_found -> canon [(nt, ts')::m]
      ]
  ;
  value lookup nt m =
    match List.assoc nt m with [
        l -> l
      | exception Not_found -> TS.mt
      ]
  ;
  value add m (nt, tok) = addset m (nt, TS.mk [tok]) ;
  value export m = m |> List.map (fun (nt, s) -> (nt, TS.export s)) ;
end ;
module SM = SetMap ;

module type MUTSETMAP = sig
  type t 'a = 'c;
  type set_t 'a = 'd ;
  value mk : unit -> t 'a ;
  value add : t 'a -> (string * 'a) -> unit ;
  value lookup : string -> t 'a -> set_t 'a ;
  value addset : t 'a -> (string * set_t 'a) -> unit ;
  value export : t 'a -> SM.t 'a ;
end ;

module MutSetMap : (MUTSETMAP with type set_t 'a = TS.t 'a) = struct
  type t 'a = ref (SM.t 'a) ;
  type set_t 'a = SM.set_t 'a ;
  value mk () = ref (SM.mt) ;
  value add mm p =
    mm.val := SM.add mm.val p ;
  value lookup k mm = SM.lookup k mm.val ;
  value addset mm pl =
    mm.val := SM.addset mm.val pl ;
  value export mm = mm.val ;
end ;
module MSM = MutSetMap ;

module First = struct

value rec psymbols m = fun [
  [] -> TS.mk [None]
| [h::t] ->
   let fh = psymbol m h in
   if TS.mem None fh then
     TS.(union (except None fh) (psymbols m t))
   else fh
]

and psymbol m ps = symbol m ps.ap_symb

and symbol m = fun [
      ASflag _ s -> TS.(union (symbol m s) (mk[None]))
    | ASkeyw _ kw -> TS.mk [Some (SPCL kw)]
    | ASlist loc lml elem_s sepb_opt ->
       let felem = symbol m elem_s in
       if not (TS.mem None felem) then felem
       else
         TS.(union (except None felem) (
         match sepb_opt with [
             None -> mk [None]
           | Some (sep_s, _) ->
              symbol m sep_s
       ]))

    | ASnext _ _ -> assert False

    | ASnterm _ nt _ _ -> SM.lookup nt m
    | ASopt _ s -> TS.(union (mk [None]) (symbol m s))

  | ASleft_assoc _ s1 s2 _ ->
     let fs1 = symbol m s1 in
     if not (TS.mem None fs1) then fs1
     else TS.(union (except None fs1) (symbol m s2))

  | ASrules _ rl -> rules m rl
  | ASself _ _ -> assert False
  | AStok _ cls _ -> TS.mk[Some (CLS cls)]
  | ASvala _ s sl ->
     TS.(union (symbol m s) (sl |> List.concat_map (fun s -> [Some (SPCL s); Some (SPCL ("_"^s))]) |> mk))
]

and rule m r = psymbols m r.ar_psymbols

and rules m l =
  let rules = l.au_rules in
  TS.unionl (List.map (rule m) rules)
;

value level m l = rules m l.al_rules ;

value comp1_entry m e =
  e.ae_levels
  |> List.map (level m)
  |> TS.unionl
  |> (fun ts -> SM.addset m (e.ae_name, ts))
;

value comp1 el m = List.fold_left comp1_entry m el ;

value rec comprec el m =
  let m' = comp1 el m in
  if m = m' then m else comprec el m'
;

value compute_first el = comprec el SM.mt ;
  
value exec0 el = compute_first el ;
value exec (loc, gl, el) = SM.export (exec0 el) ;

end ;

module Follow = struct

value nullable l = TS.mem None l ;

(** [fifo_concat ~{must} ~{if_nullable} fi fo]

    when must is true: concat fi.fo, removing eps if present.

    when must is false:

    when if_nullable is true, concats fi.fo IF fi is nullable.

    when if_nullable is false, checks that fi is NOT nullable, and concats.

 *)
value fifo_concat loc ?{must=False} ?{if_nullable=False} fi fo =
  match (must, if_nullable, nullable fi) with [
      (True, True, _) ->
      raise_failwithf loc "fifo_concat: incompatible arguments with must=True, if_nullable=True"
    | (_, True, True) -> TS.(union (map Std.outSome (TS.except None fi)) fo)
    | (_, True, False) -> TS.map Std.outSome fi
    | (_, False, True) ->
       raise_failwithf loc "fifo_concat: [fi] is nullable, but if_nullable=False"
    | (_, False, False) -> TS.(union (TS.map Std.outSome fi) fo)
    ]
;

value fi2fo loc fi = fifo_concat loc ~{must=True} fi TS.mt ;

(** Compute "FI-FO" First(s).[Follow(s) when first contains epsilon].

    We pass:

    fimap: map for computing FIRST
    mm: the current mutable map of FOLLOW
    ff: "full follow" of whatever might follow the current symbol

    Procedure:

    We invoke fifo on all sub-symbols.  When invoked on a nonterminal, we
    add "full follow" to the FOLLOW set of the nonterminal.

 *)

value rec fifo_psymbols (fimap, mm) ff = fun [
      [] -> ff
    | [h::t] ->
       let ft = fifo_psymbols (fimap, mm) ff t in
       fifo_psymbol (fimap, mm) ft h
       
]

and fifo_psymbol (fimap, mm) ff ps =
  fifo_symbol (fimap, mm) ff ps.ap_symb

(** [fifo_symbol (fimap, mm) ff]

    fimap: the result of First.exec, the map from nonterminal to
   FIRST-set mm: mutable map of FOLLOW sets ff: full-follow for the
   current symbol in the current production

    "full follow" means the current best approximation of the
   follow-set for this symbol in this production.

    For FLAG/OPT/LIST composite symbols, we check that they are not nullable,
    but the code should be OK with them being nullable.  I don't know any
    good reason why they should be nullable ( *esp* for LIST) but I'll leave
    the code as-is until I get a really good reason to change it.

 *)

and fifo_symbol (fimap, mm) ff = fun [
      ASflag loc s | ASopt loc s ->
      (* the fifo of [FLAG s] is always the concat of the FIRST of s
         (minus eps) and the full-follow of [FLAG s], since [FLAG s]
         is nullable.
       *)
      let _ = fifo_symbol (fimap, mm) ff s in
      let fi_s = First.symbol fimap s in do {
        if nullable fi_s then
          raise_failwith loc "FLAG/OPT must not be nullable"
        else
          fifo_concat ~{must=True} loc fi_s ff
      }

    | ASkeyw _ kw -> TS.mk[(SPCL kw)]

    | ASlist loc lml s sepopt_opt ->
       (* A. if a LIST has element that is NOT nullable, OR is LIST0,
          then the fifo is just the firsts of that element.

          B. if the element is nullable, then combine fifo_element,
          fifo_sep (if any) and full-follow

          Procedure: by cases:
           
          0. call [ff] argument "full-follow"
        *)

       let fi_s = First.symbol fimap s in
       if nullable fi_s then
         raise_failwithf loc "LIST element must not be nullable"
       else
       match (lml, sepopt_opt) with [
           (*
             1. LIST1, no SEP:

                a. fifo is [FIRST s].{if_nullable}.full-follow
                b. compute [FIFO s] with ff=[FIRST s].full-follow
            *)

           (LML_1, None) ->

           let _ = 
             let ff = fifo_concat loc ~{must=True} fi_s ff in
             fifo_symbol (fimap, mm) ff s in

           fifo_concat loc ~{if_nullable=True} fi_s ff

         (*
           2. LIST1, mandatory SEP s2:

             a. fifo is [FIRST s].{if_nullable}.(([FIRST s2].[]) union full-follow)
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.([FIRST s2].full-follow)
          *)

         | (LML_1, Some (s2, False)) ->
           let fi_s2 = First.symbol fimap s2 in
           if nullable fi_s2 then
             raise_failwithf loc "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat loc ~{if_nullable=True} fi_s2 (fi2fo loc fi_s)) ff) in
             fifo_symbol (fimap, mm) ff s in

           let _ =
             let ff = (fifo_concat loc ~{if_nullable=True} fi_s (fifo_concat loc fi_s2 ff)) in
             fifo_symbol (fimap, mm) ff s2 in

           fifo_concat loc ~{if_nullable=True} fi_s (TS.union (fi2fo loc fi_s2) ff)

         (*

          2'. LIST1, optional last SEP s2:

             a. fifo is [FIRST s].{if_nullable}.([FIRST s2] union full-follow)
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.[FIRST s2] union full-follow
          *)

         | (LML_1, Some (s2, True)) ->
           let fi_s2 = First.symbol fimap s2 in
           if nullable fi_s2 then
             raise_failwithf loc "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat loc ~{if_nullable=True} fi_s2 (fi2fo loc fi_s)) ff) in
             fifo_symbol (fimap, mm) ff s in

           let _ =
             let ff = TS.(union (fifo_concat loc ~{if_nullable=True} fi_s (fi2fo loc fi_s2)) ff) in
             fifo_symbol (fimap, mm) ff s2 in

           fifo_concat loc ~{if_nullable=True} fi_s (TS.union (fi2fo loc fi_s2) ff)

         (*
          3. LIST0, no SEP:

             a. fifo is [FIRST s].full-follow
             b. compute [FIFO s] with ff=[FIRST s].full-follow
          *)

         | (LML_0, None) ->
           let _ = 
             let ff = fifo_concat loc ~{must=True} fi_s ff in
             fifo_symbol (fimap, mm) ff s in

           fifo_concat loc ~{must=True} fi_s ff

         (*
          4. LIST0, mandatory SEP s2:

             a. fifo is [FIRST s].{if_nullable}.([FIRST s2].[]) union full-follow
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.[FIRST s2]
          *)

         | (LML_0, Some (s2, False)) ->
           let fi_s2 = First.symbol fimap s2 in
           if nullable fi_s2 then
             raise_failwithf loc "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat loc ~{if_nullable=True} fi_s2 (fi2fo loc fi_s)) ff) in
             fifo_symbol (fimap, mm) ff s in

           let _ =
             let ff = (fifo_concat loc ~{if_nullable=True} fi_s (fifo_concat loc fi_s2 ff)) in
             fifo_symbol (fimap, mm) ff s2 in

           TS.(union (fifo_concat loc ~{if_nullable=True} fi_s (fi2fo loc fi_s2)) ff)

         (*
          4. LIST0, optional last SEP s2:

             a. fifo is [FIRST s].{if_nullable}.([FIRST s2].[]) union full-follow
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.[FIRST s2] union full-follow
          *)

         | (LML_0, Some (s2, True)) ->
           let fi_s2 = First.symbol fimap s2 in
           if nullable fi_s2 then
             raise_failwithf loc "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat loc ~{if_nullable=True} fi_s2 (fi2fo loc fi_s)) ff) in
             fifo_symbol (fimap, mm) ff s in

           let _ =
             let ff = TS.(union (fifo_concat loc ~{if_nullable=True} fi_s (fi2fo loc fi_s2)) ff) in
             fifo_symbol (fimap, mm) ff s2 in

           TS.(union (fifo_concat loc ~{if_nullable=True} fi_s (fi2fo loc fi_s2)) ff)

         ]

  | ASnext loc _ | ASself loc _ -> raise_failwithf loc "fifo_symbol: internal error: NEXT should not occur here"
  | ASnterm loc nt _ _ as s -> do {
        MSM.addset mm (nt, ff) ;
        let fi_s = First.symbol fimap s in
        fifo_concat loc ~{if_nullable=True} fi_s ff
      }

  | ASleft_assoc loc s1 s2 _ ->
  (* 1. fifo is [FIRST s1].{is_nullable}.[FIRST s2].{is_nullable}.full-follow
     2. compute [FIFO s1] with ff=[FIRST s2].{is_nullable}.full-follow
     3. compute [FIFO s2] with ff=[FIRST s2].{is_nullable}.full-follow
   *)                               
     let fi_s1 = First.symbol fimap s1 in
     let fi_s2 = First.symbol fimap s2 in

     let _ =
       let ff = fifo_concat loc ~{if_nullable=True} fi_s2 ff in
       fifo_symbol (fimap, mm) ff s1 in

     let _ =
       let ff = fifo_concat loc ~{if_nullable=True} fi_s2 ff in
       fifo_symbol (fimap, mm) ff s2 in

     fifo_concat loc ~{if_nullable=True} fi_s1
       (fifo_concat loc ~{if_nullable=True} fi_s2 ff)

  | ASrules loc rs ->
     fifo_rules (fimap, mm) ff rs

  | AStok loc cls _ -> TS.mk [CLS cls]

  | ASvala loc s sl as s0 ->
     let _ = fifo_symbol (fimap, mm) ff s in

     let fi_vala = First.symbol fimap s0 in
     fifo_concat loc ~{if_nullable=True} fi_vala ff

]

and fifo_rule (fimap, mm) ff r =
  fifo_psymbols (fimap, mm) ff r.ar_psymbols

and fifo_rules (fimap, mm) ff rs =
  let loc = rs.au_loc in
  let rl = rs.au_rules in
  let fi_rs = rl |> List.map (First.rule fimap) |> TS.unionl in do {
    rl |> List.iter (fun r ->
              ignore (fifo_rule (fimap, mm) ff r)) ;
    fifo_concat loc ~{if_nullable=True} fi_rs ff
  }

and fifo_level (fimap, mm) ff lev =
  fifo_rules  (fimap, mm) ff lev.al_rules
;

value comp1_entry (fimap, mm) e =
  let ll = e.ae_levels in do {
  assert (1 = List.length ll) ;
  let e_ff = MSM.lookup e.ae_name mm in
  ignore (fifo_level (fimap, mm) e_ff (List.hd ll))
}
;
  

value comp1 (fimap, mm) el =
  List.iter (comp1_entry (fimap, mm)) el ;

value rec comprec el (fimap, mm) = do {
  let m0 = mm in
  comp1 (fimap, mm) el ;
  if m0 = mm then MSM.export m0 else comprec el (fimap, mm) ;
}
;

value exec0 ~{top} el =
  let fimap = First.exec0 el in
  let mm = MSM.mk () in do {
    if None <> top then MSM.(add mm (Std.outSome top, CLS "EOI")) else ();
    (fimap, comprec el (fimap, mm))
  }
;

value exec ?{top} (loc, gl, el) = exec0 ~{top=top} el ;

end ;

module S5LambdaLift = struct
  (** in each entry, replace all multi-way rules with a new entry;
      repeat until there are no multi-way rules left in any entry.
   *)

module Ctr = struct
  type t = ref int ;
  value mk () = ref 0 ;
  value next ctr = let rv = ctr.val in do { incr ctr ; rv } ;

  value fresh_name root ctr =
    let n = next ctr in
    Fmt.(str "%s__%02d" root n) ;
end ;


value rec lift_rules mut esig rl = { (rl) with au_rules = List.map (lift_rule mut esig) rl.au_rules }

and lift_rule mut esig r =
  let (_, revps) = List.fold_left (fun (stkpat, revps) ps ->
    let ps = lift_psymbol mut esig stkpat ps in
    let stkpat = match ps.ap_patt with [ None -> stkpat | Some p -> [p :: stkpat] ] in
    (stkpat, [ps :: revps])
  ) ([], []) r.ar_psymbols in
  { (r) with ar_psymbols = List.rev revps }

and lift_psymbol mut esig stkpat ps =
  { (ps) with ap_symb = lift_symbol mut esig stkpat ps.ap_symb }

and lift_symbol ((ctr, acc) as mut) ((ename, eformals) as esig) revpats = fun [
      ASflag loc s -> ASflag loc (lift_symbol mut esig revpats s)
  | ASkeyw _ _ as s -> s

  | ASlist loc lml s None ->
     ASlist loc lml (lift_symbol mut esig revpats s) None
  | ASlist loc lml s (Some (s2, b)) ->
     ASlist loc lml (lift_symbol mut esig revpats s) (Some (lift_symbol mut esig revpats s2, b))

  | ASnext _ _ as s -> s
  | ASnterm _ _ _ _ as s -> s
  | ASopt loc s -> ASopt loc (lift_symbol mut esig revpats s)

  | ASleft_assoc loc s1 s2 e ->
     ASleft_assoc loc (lift_symbol mut esig revpats s1) (lift_symbol mut esig revpats s2) e

  | ASrules loc rl ->
     let formals = eformals @ (List.rev revpats) in
     let actuals = formals2actuals formals in
     let new_ename = Ctr.fresh_name ename ctr in
     let new_e = {
         ae_loc = rl.au_loc
       ; ae_name = new_ename
       ; ae_pos = None
       ; ae_formals = formals
       ; ae_levels = [{al_loc = rl.au_loc; al_label = None ; al_assoc = None ; al_rules = rl}]
       } in do {
        Std.push acc new_e ;
        ASnterm rl.au_loc new_ename actuals None
      }

  | ASself _ _ as s -> s
  | AStok _ _ _ as s -> s
  | ASvala loc s sl -> ASvala loc (lift_symbol mut esig revpats s) sl
]
;

value lift_level mut esig l = { (l) with al_rules = lift_rules mut esig l.al_rules } ;

value lift_levels mut esig ll = do {
    assert (1 = List.length ll) ;
    List.map (lift_level mut esig) ll
}    
;
value lift_entry mut e =
  let ll = lift_levels mut (e.ae_name, e.ae_formals) e.ae_levels in
  { (e) with ae_levels = ll }
;
  
value exec0 el =
  let ctr = Ctr.mk() in 
  let rec erec el =
    let acc = ref [] in
    let el = List.map (lift_entry (ctr, acc)) el in
    if [] = acc.val then el
    else erec (el @ acc.val)
  in erec el
;

value exec (loc, gl, el) = (loc, gl, exec0 el) ;

end ;

module SortEntries = struct

value exec0 el =
  let cmp e1 e2 = String.compare e1.ae_name e2.ae_name in
  List.stable_sort cmp el ;

value exec (loc, gl, el) =  (loc, gl, exec0 el) ;

end ;

(** An empty entry is one of the form:

  e[args]: [ [ x = f[args] -> x ] ] ;

  Such an entry can be eliminated, and all instances of entry "e"
  can be replaced with "f".
 *)
module S3EmptyEntryElim = struct

value empty_rule (ename, formals) = fun [
      {ar_psymbols=[{ap_patt= Some <:patt< $lid:patt_x$ >>; ap_symb=ASnterm _ rhsname actuals None}];
       ar_action = Some <:expr< $lid:expr_x$ >> } ->
      if List.length formals = List.length actuals &&
           List.for_all2 equal_expr (formals2actuals formals) actuals then
        Some (ename, rhsname)
      else None
    | _ -> None
    ]
;

value empty_level (ename, formal) l =
  if 1 = List.length l.al_rules.au_rules then
    empty_rule (ename, formal) (List.hd l.al_rules.au_rules)
  else None
;

value gen_re = Pcre.regexp "^([a-zA-Z0-9_]+)__([0-9]{4})(__[0-9]{2})?$" ;
value is_generated_entry_name n = Pcre.pmatch ~{rex=gen_re} n ;

value find_empty_entry el =
  el |> List.find_map (fun e ->
      let ename = e.ae_name in
      let formals = e.ae_formals in
      if is_generated_entry_name e.ae_name && 1 = List.length e.ae_levels then
        empty_level (ename, formals) (List.hd e.ae_levels)
      else None
  )
;

value eliminate_empty_entry (lhs, rhs) e =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm loc nt actuals None when lhs = nt -> ASnterm loc rhs actuals None
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol } in
  dt.migrate_a_entry dt e
;

value rec exec0 el =
    match find_empty_entry el with [
        None -> el
      | Some (ename, rhsname) ->
         let rest_el = List.filter (fun e' -> ename <> e'.ae_name) el in
         exec0 (List.map (eliminate_empty_entry (ename, rhsname)) rest_el)
    ]
;

value exec (a,b,c) = (a,b, exec0 c) ;

end ;

(** Codegen:

  0. compute the set of all tokens/classes.
  1. Each entry A has at most a disjunction of rules.
  2. for each production "A -> w":

  3. compute [FIRST w].{if_nullable}.[FOLLOW A] for each production

  4. each branch of the parsing function gets its patterns from the intersection of #0 and #3.
 *)

module Codegen = struct
open Token_regexps ;
open PatternBaseToken ;

value all_tokens el =
  let open Llk_migrate in
  let acc = ref [] in
  let dt = make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt s = do { match s with [
          ASkeyw _ s0 -> Std.push acc (SPCL s0)
        | AStok _ s0 None -> Std.push acc (CLS s0)
        | AStok loc s (Some _) -> raise_failwith loc "unupported"
        | ASvala _ s0 sl -> do {
            ignore (dt.migrate_a_symbol dt s0) ;
            List.iter (fun s2 -> Std.push acc (SPCL s2)) sl ;
            List.iter (fun s2 -> Std.push acc (SPCL ("_"^s2))) sl
          }
        | s -> ignore(fallback_migrate_a_symbol dt s)
        ];
        s
      }
  in
  let dt = { (dt) with migrate_a_symbol = migrate_a_symbol } in do {
    List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) el ;
    List.sort_uniq Stdlib.compare acc.val
  }
;

value token_to_pattern loc = fun [
    CLS s -> <:patt< ($str:s$, _) >>
  | SPCL s -> <:patt< ("", $str:s$) >>
]
;

value compute_fifo loc fimap ff r =
  let fi = First.rule fimap r in
  (fi, ff, r)
;

value disjoint loc ll =
  let rec drec acc = fun [
        [] -> True
      | [(fi, ff,_) :: t] ->
         let h = Follow.fifo_concat loc ~{if_nullable=True} fi ff in
         TS.disjoint acc h
         && drec (TS.union h acc) t
      ] in
  drec TS.mt ll
;

value tokens_to_patt loc l = 
  let patts = List.map (token_to_pattern loc) l in
  List.fold_left (fun p q -> <:patt< $p$ | $q$ >>)
    (List.hd patts) (List.tl patts)
;

value rec compile1_symbol loc (fimap,fomap) ename s =
  match s with [
      ASflag loc s -> do {
      let tokens = Follow.fifo_concat loc (First.symbol fimap s) (TS.mk[]) in
        assert (TS.mt <> tokens) ;
        let s_body = compile1_symbol loc (fimap, fomap) ename s in
        <:expr< parser [ [: _ = $s_body$ :] -> True | [: :] -> False ] >>
      }

    | ASkeyw  loc kws ->
       <:expr< parser [ [: `("", $str:kws$) :] -> () ] >>

    | ASnterm loc nt actuals None ->
       Expr.applist <:expr< $lid:nt$ >> (actuals@[<:expr< __strm__ >>])

    | AStok loc cls None ->
       <:expr< parser [ [: `($str:cls$, __x__) :] -> __x__ ] >>

(*
    | ASleft_assoc loc lhs restrhs e ->
 *)       
    ]
;
(*
let left_assoc lhs restrhs combe =
  parser [
   [: x = lhs ; rv = parser [ [: y = restrhs :] -> combe x y | [: :] -> x ] :] -> rv
    ]
 *)
value compile1_rule (fimap,fomap) ename r =
  let loc = r.ar_loc in
  List.fold_right (fun ps body ->
      let ps_patt = match ps.ap_patt with [ None -> <:patt< _ >> | Some p -> p ] in
      let ps_symbol = compile1_symbol ps.ap_loc (fimap,fomap) ename ps.ap_symb in
      <:expr< parser [ [: $ps_patt$ = $ps_symbol$ ; __strm_ :] -> $body$ ] >>)
    r.ar_psymbols
    (match r.ar_action with [ None -> <:expr< () >> | Some a -> a ])
;

value compile1_branch (fimap,fomap) ename (fi, fo, r) =
  let loc = r.ar_loc in
  let body = compile1_rule (fimap,fomap) ename r in
  if not (Follow.nullable fi) then
    let raw_tokens = TS.export (Follow.fi2fo loc fi) in
    let patt = tokens_to_patt loc raw_tokens in
    let tokens = List.map Std.inSome raw_tokens in
    (tokens, r, (<:patt< Some $patt$ >>, <:vala< None >>, body))
  else if TS.mt <> fo then
    let raw_tokens = TS.export (Follow.fifo_concat loc ~{if_nullable=True} fi fo) in
    let patt = tokens_to_patt loc raw_tokens in
    let tokens = List.map Std.inSome raw_tokens in
    (tokens, r, (<:patt< Some $patt$ >>, <:vala< None >>, body))
    else
      ([None], r, (<:patt< _ >>, <:vala< None >>, body))
;

value reorder_branches l =
  let (concrete_branches, fallthru_branches) =
    filter_split (fun (tl, _, _) -> List.for_all Std.isSome tl) l in
  concrete_branches @ fallthru_branches
;

value compile1_entry (fimap, fomap) e =
  let loc = e.ae_loc in
  let ename = e.ae_name in
  let ff = SM.lookup ename fomap in
  let fi_fo_rule_list =
    (List.hd e.ae_levels).al_rules.au_rules
    |> List.map (compute_fifo loc fimap ff) in do {
    if not (disjoint loc fi_fo_rule_list) then
      raise_failwithf loc "compile1_entry: FIFO sets were not disjoint"
    else if TS.mt = ff 
       && 1 < List.length (List.filter (fun (fi, _, _) -> Follow.nullable fi) fi_fo_rule_list) then
      raise_failwith loc "compile1_entry: more than one branch is nullable"
    else () ;
    let tokens_rule_branches =
      fi_fo_rule_list
    |> List.map (compile1_branch (fimap,fomap) ename) in
    let tokens_rule_branches = reorder_branches tokens_rule_branches in
    let branches = List.map Std.third3 tokens_rule_branches in
    let rhs =
      match branches with [
        [(_,_,e)] -> e
      | [] -> assert False
      | _ ->
         let rhs = <:expr< fun __strm__ -> match Stream.peek __strm__ with [ $list:branches$ ] >> in
         List.fold_right (fun p rhs -> <:expr< fun $p$ -> $rhs$ >>) e.ae_formals rhs ]
    in
    (<:patt< $lid:ename$ >>, rhs, <:vala< [] >>)
  }
;

value exec ?{top} (loc, gl, el) =
  let (fimap, fomap) = Follow.exec0 ~{top=top} el in
  let fdefs = List.map (compile1_entry (fimap, fomap)) el in
  <:str_item< value rec $list:fdefs$ >>
;
end ;

module Top = struct
open Pa_llk ;

value parse s =
  s
  |> RT.(with_file pa)
  |> CheckLexical.exec
;

value coalesce s =
  s
  |> parse
  |> S1Coalesce.exec
;

value precedence s =
  s
  |> coalesce
  |> CheckLexical.exec
  |> S2Precedence.exec
;

value empty_entry_elim s =
  s
  |> precedence
  |> CheckLexical.exec
  |> CheckNoPosition.exec
  |> CheckNoLabelAssocLevel.exec
  |> S3EmptyEntryElim.exec
;

value left_factorize s =
  s
  |> empty_entry_elim
  |> S4LeftFactorize.exec
;

value lambda_lift s =
  s
  |> left_factorize
  |> CheckLexical.exec
  |> S5LambdaLift.exec
  |> CheckLexical.exec
  |> SortEntries.exec
;

value first s =
  s
  |> lambda_lift
  |> First.exec
;

value follow ~{top} s =
  s
  |> lambda_lift
  |> Follow.exec ~{top=top}
;

value codegen s =
  s
  |> lambda_lift
  |> SortEntries.exec
  |> Codegen.exec
;

end ;
