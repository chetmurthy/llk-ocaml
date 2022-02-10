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
module Coalesce = struct
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

  value exec (loc, gl, el) = (loc, gl, coalesce_entries el) ;

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

module Precedence = struct 
  open Pa_ppx_utils ;
open Ppxutil ;

value lookup_rho s rho : a_symbol = AList.assoc ~{cmp=equal_a_symbol} s rho ;


value rec substitute1_symbol rho = fun [
      ASflag loc s -> ASflag loc (substitute1_symbol rho s)
  | ASkeyw _ _ | AStok _ _ _ as s -> s
  | ASlist loc lml s1 sb_opt ->
     ASlist loc lml
       (substitute1_symbol rho s1)
       (Option.map (fun (s,b) -> (substitute1_symbol rho s1,b)) sb_opt)

  | (ASnterm _ _ _ | ASnext _ | ASself _) as s -> match lookup_rho s rho with [
                          s -> s
                        | exception Not_found -> s
                        ]
  | ASopt loc s -> ASopt loc (substitute1_symbol rho s)
  | ASleft_assoc loc s1 s2 e ->
     ASleft_assoc loc (substitute1_symbol rho s1) (substitute1_symbol rho s2) e
  |  ASrules loc rs -> ASrules loc {(rs) with au_rules = substitute1_rules rho rs.au_rules}
   
  
  | ASvala loc s sl -> ASvala loc (substitute1_symbol rho s) sl
  ]

and substitute1_psymbol rho ps =
  {(ps) with ap_symb = substitute1_symbol rho ps.ap_symb}

and substitute1_rule rho r =
  {(r) with ar_psymbols = List.map (substitute1_psymbol rho) r.ar_psymbols }

and substitute1_rules rho rl = List.map (substitute1_rule rho) rl ;

value rewrite_righta loc ename ~{cur} ~{next} rho rl =
  let right_rho = [
      (ASself loc, ASnterm loc cur None)
     ;(ASnterm loc ename None, ASnterm loc cur None)
    ] in
  let rl =
    rl
    |> List.map (fun r ->
           let psl = r.ar_psymbols in
           let (last, psl) = Std.sep_last psl in
           let psl = List.map (substitute1_psymbol rho) psl in
           let last = substitute1_psymbol right_rho last in
           let psl = psl @ [last] in
           {(r) with ar_psymbols = psl}
         ) in
  let last_rule = {ar_loc = loc;
                   ar_psymbols = [{ap_loc = loc;
                                   ap_patt = Some <:patt< x >> ;
                                   ap_symb = ASnterm loc next None}];
                   ar_action = Some <:expr< x >> } in
  rl @ [last_rule]
;

value rewrite_lefta loc ename ~{cur} ~{next} rho rl =
  let left_rho = [
      (ASself loc, ASnterm loc next None)
     ;(ASnterm loc ename None, ASnterm loc next None)
    ] in
  let (left_patt, left_symbol) = match (List.hd rl).ar_psymbols with [
        [{ap_patt=x; ap_symb = y}::_] -> (x,y)
      ] in
  let left_patt = match left_patt with [ None -> <:patt< _ >> | Some p -> p ] in
  let right_rl =
    rl
  |> List.map (fun r ->
         {(r) with ar_psymbols = List.tl r.ar_psymbols ;
                   ar_action = r.ar_action |> Option.map (fun act -> <:expr< fun [ $left_patt$ -> $act$ ] >>)
         }) in
  let right_rl = substitute1_rules rho right_rl in
  let left_symbol = substitute1_symbol left_rho left_symbol in
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

value rewrite1 e ename ~{cur} ~{next} dict l = do {
    assert ([] <> l.al_rules.au_rules) ;
    let loc = l.al_loc in
    let l = match l.al_assoc with [
          None | Some NONA ->
            let rules =
              l.al_rules.au_rules
              |> substitute1_rules [
                     (ASnext loc, ASnterm loc next None)
                    ;(ASself loc, ASnterm loc next None)
                    ;(ASnterm loc ename None, ASnterm loc next None)
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
               failwith Fmt.(str "rewrite1: entry %s RIGHTA level rules must all have at least 2 psymbols"
                               ename)
             else () ;
             let (last_psymbol, _) = Std.sep_last (List.hd rl).ar_psymbols in
             if not (rl |> List.for_all (fun r -> 
                               equal_a_psymbol last_psymbol (fst (Std.sep_last r.ar_psymbols)))) then
               failwith Fmt.(str "rewrite1: entry %s RIGHTA level does not have identical last psymbols"
                               ename)
             else () ;
             match last_psymbol.ap_symb with [
                 ASnterm _ name None when name = ename -> ()
               | ASself _ -> ()
               | _ -> failwith Fmt.(str "rewrite1: entry %s RIGHTA level has last psymbol non-recursive"
                                      ename)
               ] ;
             let rl = rewrite_righta loc ename ~{cur=cur} ~{next=next} [
                          (ASnext loc, ASnterm loc next None)
                         ;(ASself loc, ASnterm loc next None)
                         ;(ASnterm loc ename None, ASnterm loc next None)
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
               failwith Fmt.(str "rewrite1: entry %s LEFTA level rules must all have at least 2 psymbols"
                               ename)
             else () ;
             let first_psymbol = List.hd (List.hd rl).ar_psymbols in
             if not (rl |> List.for_all (fun r -> 
                               equal_a_psymbol first_psymbol (List.hd r.ar_psymbols))) then
               failwith Fmt.(str "rewrite1: entry %s LEFTA level does not have identical first psymbols"
                               ename)
             else () ;
             match first_psymbol.ap_symb with [
                 ASnterm _ name None when name = ename -> ()
               | ASself _ -> ()
               | _ -> failwith Fmt.(str "rewrite1: entry %s LEFTA level has first psymbol non-recursive"
                                      ename)
               ] ;
             let rl = rewrite_lefta loc ename ~{cur=cur} ~{next=next} [
                          (ASnext loc, ASnterm loc next None)
                         ;(ASself loc, ASnterm loc next None)
                         ;(ASnterm loc ename None, ASnterm loc next None)
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
  {ae_loc = loc; ae_name = from_name; ae_pos = None;
   ae_levels =
     [{al_loc = loc; al_label = None; al_assoc = None;
       al_rules =
         {au_loc = loc;
          au_rules =
            [{ar_loc = loc;
              ar_psymbols = [{ap_loc = loc;
                              ap_patt = Some <:patt< x >> ;
                              ap_symb = ASnterm loc to_name None}];
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
  let levels = e.ae_levels in
  let n_levels = List.length levels in
  let named_levels =
    List.mapi (fun i l -> (i+1, new_name e (i+1), l)) levels in
  let dict =
    named_levels
    |> List.filter_map (fun (i, newname, l) ->
           match l.al_label with [
               None -> None
             | Some lab -> Some (ASnterm l.al_loc ename (Some lab), ASnterm l.al_loc newname None)
         ]) in
  let newents =
    named_levels
    |> List.map (fun (i, newname, l) ->
           rewrite1 e ename ~{cur=newname} ~{next=new_name e (i+1)} dict l) in
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

value exec0 e =
  if List.length e.ae_levels <=1 then ([], [e])
  else exec1 e ;

value exec (loc, gl, el) =
  let pl = List.map exec0 el in
  let dict = pl |> List.concat_map fst in
  let el = List.concat_map snd pl in
  (loc, gl, el)
;

end ;

module LeftFactorize = struct

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

value left_factorize loc rl =
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

value rec left_factorize_level l =
  let loc = l.al_loc in
  let rl = left_factorize_rules l.al_rules.au_rules in
  {(l) with
    al_rules = {(l.al_rules) with au_rules = left_factorize loc rl } }

and left_factorize_levels l = do {
  assert (1 = List.length l) ;
  List.map left_factorize_level l
}

and left_factorize_rules (rl : list a_rule) = List.map left_factorize_rule rl
and left_factorize_rule r = { (r) with ar_psymbols = List.map left_factorize_psymbol r.ar_psymbols }
and left_factorize_psymbol ps = { (ps) with ap_symb = left_factorize_symbol ps.ap_symb }
and left_factorize_symbol = fun [
    (ASkeyw _ _ | ASnext _ | ASnterm _ _ _ | ASself _ | AStok _ _ _) as s -> s

  | ASflag loc s -> ASflag loc (left_factorize_symbol s)

  | ASlist loc lml s sb_opt ->
     ASlist loc lml
       (left_factorize_symbol s)
       (Option.map (fun (s, b) -> (left_factorize_symbol s, b)) sb_opt)

  | ASopt loc s -> ASopt loc (left_factorize_symbol s)

  | ASleft_assoc loc s1 s2 e -> ASleft_assoc loc (left_factorize_symbol s1) (left_factorize_symbol s2) e

  | ASrules loc rl -> ASrules loc {(rl) with au_rules = left_factorize_rules rl.au_rules }
  | ASvala loc s sl -> ASvala loc (left_factorize_symbol s) sl
]
;

value exec0 e = {(e) with ae_levels = left_factorize_levels e.ae_levels } ;

value exec (loc, gl, el) = (loc, gl, List.map exec0 el) ;

end ;
