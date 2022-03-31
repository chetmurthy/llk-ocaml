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
open Coll ;
open Ppxutil ;

open Primtypes ;
open Llk_regexps ;
open Llk_types ;
open Print_gram ;

value entry_name e = e.ae_name ;
value entry_labels e =
  e.ae_levels
  |> List.filter_map (fun [ {al_label=Some l} -> Some l | _ -> None ]) ;

value entry_position e = e.ae_pos ;
value entry_location e = e.ae_loc ;

type token = Llk_regexps.PatternBaseToken.t == [ CLS of string and option string | SPCL of string | ANTI of string | OUTPUT of int ]
;

value print_token_option = fun [
    None -> "eps"
|   Some t -> PatternBaseToken.print t
]
;

module Ctr = struct
  type t = { it : Hashtbl.t string (ref int) } ;
  value mk () = { it = Hashtbl.create 23 } ;
  value find {it=it} s =
    match Hashtbl.find it s with [
        x -> x
      | exception Not_found -> do {
          let v = ref 1 in
          Hashtbl.add it s v ;
          v
        }
      ]
  ;
  value next ctr = let rv = ctr.val in do { incr ctr ; rv } ;
  value fresh_name root it =
    let r = find it (fst root) in
    let n = next r in
    Name.fresh root n
  ;
end ;

module type TOKENSET = sig
(*
  type t 'a = 'b ;
 *)
  type t 'a = list 'a ;

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
  value print : ('a -> string) -> t 'a -> string ;
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
  value print pf l = Printf.sprintf "[%s]" (String.concat " " (List.map pf l)) ;
end ;
module TS = TokenSet ;

module type SETMAP = sig
(*
  type t 'a = 'c;
  type set_t 'a = 'd ;
 *)
  type set_t 'a = TS.t 'a ;
  type t 'a = list (Name.t * set_t 'a) ;

  value canon : t 'a -> t 'a ;
  value mt : t 'a ;
  value add : t 'a -> (Name.t * 'a) -> t 'a ;
  value lookup : Name.t -> t 'a -> set_t 'a ;
  value addset : t 'a -> (Name.t * set_t 'a) -> t 'a ;
  value export : t 'a -> list (Name.t * list 'a) ;
end ;

module SetMap : (SETMAP with type set_t 'a = TS.t 'a) = struct
  type set_t 'a = TS.t 'a ;
  type t 'a = list (Name.t * set_t 'a) ;

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
(*
  type t 'a = 'c;
  type set_t 'a = 'd ;
 *)
  type set_t 'a = TS.t 'a ;
  type t 'a = ref (list (Name.t * set_t 'a)) ;

  value mk : unit -> t 'a ;
  value add : t 'a -> (Name.t * 'a) -> unit ;
  value lookup : Name.t -> t 'a -> set_t 'a ;
  value addset : t 'a -> (Name.t * set_t 'a) -> unit ;
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

module ATN0 = struct

module Node = struct
  type t = [ NODE of int ] ;
  value mk n = NODE n ;
  value print = fun [ NODE n -> Fmt.(str "%d" n) ] ;
end ;

module Raw = struct
type edge_t = (Node.t * option token * Node.t) ;

type t = {
  next_node : ref int
; nodes : ref (list Node.t)
; node_labels : MHM.t Node.t string
; entry_map : MHM.t Name.t (Node.t * Node.t)
; entry_branch_map : MHM.t (Name.t * int) Node.t
; final_nodes : mutable list Node.t
; initial_nodes : mutable list Node.t
; bhole_nodes : MHS.t Node.t
; edges: mutable list edge_t
; edges_ht: MHM.t Node.t (MHM.t (option token) (ref (list Node.t)))
; tokens : MHS.t (option token)
} ;

value mk () =
  { next_node = ref 0
  ; nodes = ref []
  ; node_labels = MHM.mk 23
  ; tokens = MHS.mk 23
  ; entry_map = MHM.mk 23
  ; entry_branch_map = MHM.mk 23
  ; final_nodes = []
  ; bhole_nodes = MHS.mk 23
  ; initial_nodes = []
  ; edges = []
  ; edges_ht = MHM.mk 23
  }
;

value nodes it = it.nodes.val ;
value tokens it = MHS.toList it.tokens ;

value new_node it = do {
  let n = it.next_node.val in 
  incr it.next_node ;
  let node = Node.mk n in
  Std.push it.nodes node ;
  node
}
;

value add_node_label it n s = MHM.add it.node_labels (n, s) ;
value node_label it n =
  match MHM.map it.node_labels n with [
      x -> Some x
    | exception Not_found -> None
]
;

value new_entry it ename = do {
  assert (not (MHM.in_dom it.entry_map ename)) ;
  let snode = new_node it in
  let enode = new_node it in
  MHM.add it.entry_map (ename, (snode, enode)) ;
  add_node_label it snode Fmt.(str "ENTER %s" (Name.print ename)) ;
  add_node_label it enode Fmt.(str "EXIT %s" (Name.print ename)) ;
  (snode, enode)
}
;

value entry_nodes it ename =
 match MHM.map it.entry_map ename with [
   x -> x
 | exception Not_found -> new_entry it ename
 ]
;

value mark_final it n =
  it.final_nodes := [n :: it.final_nodes]
;

value mark_initial it n =
  it.initial_nodes := [n :: it.initial_nodes]
;

value mark_bhole it n = MHS.add n it.bhole_nodes ;
value is_bhole it n = MHS.mem n it.bhole_nodes ;

value add_edge it ((src, lab, dst) as e) = do {
    MHS.add lab it.tokens ;
    it.edges := [e :: it.edges] ;
    let src_ht = match MHM.map it.edges_ht src with [
          x -> x
        | exception Not_found -> do {
            let x = MHM.mk 23 in
            MHM.add it.edges_ht (src, x) ;
            x
          }
    ] in
    let lab_ref = match MHM.map src_ht lab with [
          x -> x
        | exception Not_found -> do {
            let x = ref [] in
            MHM.add src_ht (lab, x) ;
            x
          }
        ] in
    Std.push lab_ref dst
}
;

value edge_labels it src =
  match MHM.map it.edges_ht src with [
      src_ht -> MHM.dom src_ht
    | exception Not_found -> []
    ]
;

value traverse it src lab =
  match MHM.map it.edges_ht src with [
      src_ht ->
      (match MHM.map src_ht lab with [
           x -> x.val
         | exception Not_found -> []
      ])
    | exception Not_found -> []
    ]
;

value entry_branch it ename i =
  MHM.map it.entry_branch_map (ename, i)
;

value add_entry_branch it ename i n = do {
  assert (not (MHM.in_dom it.entry_branch_map (ename, i))) ;
  MHM.add it.entry_branch_map ((ename, i), n)
}
;

value start_entry_branch it ename i = do {
  let (snode, _) = entry_nodes it ename in
  let n' = new_node it in
  let edge = (snode, None, n') in
  add_edge it edge ;
  add_entry_branch it ename i n' ;
  add_node_label it n' Fmt.(str "%s:%d" (Name.print ename) i) ;
  n'
}
;

value dump f it = do {
  let open Printf in
  let node2string n = Node.print n in
  let node2label n =
    let s = Node.print n in
    match node_label it n with [
        None -> s
      | Some l -> Fmt.(str "%s/%s" s l)
      ] in
  let final q = List.mem q it.final_nodes in
  let initial q = List.mem q it.initial_nodes in
  let state_label q =
    let s = node2label q in
    if initial q then 
      Fmt.(str "INIT %s" s)
    else
      s
  in
  (* Header. *)
  fprintf f "digraph G {\n";
  fprintf f "rankdir = LR;\n";
  fprintf f "ratio = auto;\n";
  (* Vertices. *)
  (nodes it)
  |> List.iter (fun q ->
         fprintf f "%s [ label=\"%s\", style = solid, shape = %s ] ;\n"
           (node2string q)
           (state_label q)
           (if final q then "doublecircle" else "circle")
       );
  (* Edges. *)
    it.edges
    |> List.iter (fun (src,lab,dst) ->
           fprintf f "%s -> %s [ label=\"%s\" ] ;\n"
             (node2string src)
             (node2string dst)
             (String.escaped (match lab with [ None -> "eps" | Some t -> PatternBaseToken.print t ]))
         ) ;
    fprintf f "}\n%!"
}
;
end ;
end ;

module CompilingGrammar = struct
  type error_t = { loc : Ploc.t ; ename : Name.t ; kind : string ; msg : string ; backtrace : string } ;
  type mut_data_t = {
      ctr : Ctr.t
    ; gram_alphabet : mutable list token
    ; gram_regexps: mutable list (Name.t * regexp)
    ; gram_externals: mutable list (Name.t * regexp)
    ; firsts : mutable SM.t (option token)
    ; follows : mutable SM.t token
    ; errors : mutable list error_t
    ; atn : mutable ATN0.Raw.t
    ; eclosure : mutable MHM.t ATN0.Node.t (list ATN0.Node.t)
    ; atn_first: MHM.t Name.t (list (int * list token))
    ; atn_firstk: MHM.t Name.t (option (list (int * list (list token))))
    } ;
  type t = (Llk_types.top * mut_data_t) ;

 value fresh_name cg x = Ctr.fresh_name x (snd cg).ctr ;

  value mk t = (t, {
                  ctr = Ctr.mk()
                ; gram_alphabet = []
                ; gram_regexps = []
                ; gram_externals = []
                ; firsts = SM.mt
                ; follows = SM.mt
                ; errors = []
                ; atn = ATN0.Raw.mk ()
                ; eclosure = MHM.mk 23
                ; atn_first = MHM.mk 23
                ; atn_firstk = MHM.mk 23
               }) ;
  value g = fst ;
  value withg cg g = (g, snd cg) ;

  value add_gram_regexp cg x =
    (snd cg).gram_regexps := [x :: (snd cg).gram_regexps] ;
  value gram_regexp_asts cg = (g cg).gram_regexp_asts ;
  value gram_regexps cg = (snd cg).gram_regexps ;
  value gram_regexp cg id = List.assoc id (snd cg).gram_regexps ;
  value exists_regexp_ast cg nt = List.mem_assoc nt (g cg).gram_regexp_asts ;

  value add_gram_external cg x =
    (snd cg).gram_externals := [x :: (snd cg).gram_externals] ;
  value gram_external_asts cg = (g cg).gram_external_asts ;
  value gram_externals cg = (snd cg).gram_externals ;
  value gram_external cg id = List.assoc id (snd cg).gram_externals ;
  value exists_external_ast cg nt = List.mem_assoc nt (g cg).gram_external_asts ;

  value gram_entries cg = (g cg).gram_entries ;
  value exists_entry cg nt = List.exists (fun e -> nt = e.ae_name) (g cg).gram_entries ;
  value gram_entry cg nt =
    match List.find_opt (fun e -> nt = e.ae_name) (g cg).gram_entries with [
        None -> assert False
      | Some e -> e
      ]
  ;

  value gram_atn cg = (snd cg).atn ;
  value gram_eclosure cg = (snd cg).eclosure ;
  value gram_atn_ec cg = ((snd cg).atn, (snd cg).eclosure) ;

  value firstmap cg = (snd cg).firsts ;

  value first cg nt = do {
    assert (exists_entry cg nt) ;
    SM.lookup nt (snd cg).firsts
  };

  value add_first cg nt fi =
    (snd cg).firsts := SM.addset (snd cg).firsts (nt, fi) ;

  value followmap cg = (snd cg).follows ;

  value follow cg nt = do {
    assert (exists_entry cg nt) ;
    SM.lookup nt (snd cg).follows
  };

  value trace_follow = ref False ;
  value watch_follow ((nt : Name.t), (from:string), (ti : TS.t token)) = () ;
  value add_follow (cg : t) ~{from:string} nt fi = do {
    watch_follow (nt, from, fi) ;
    (snd cg).follows := SM.addset (snd cg).follows (nt, fi)
  }
  ;


  value adjust0_loc loc loc' =
    Ploc.(make_loc
            (file_name loc)
            (line_nb loc + line_nb loc')
            (bol_pos loc')
            (first_pos loc', last_pos loc')
            (comment loc'))
  ;
  value adjust_loc cg loc' =
    adjust0_loc (g cg).gram_loc loc'
  ;

  value errors cg = (snd cg).errors ;
  value add_error cg (loc, ename, kind, msg) =
    let bts = Printexc.(50 |> get_callstack |> raw_backtrace_to_string) in
    (snd cg).errors := [ {loc=loc; ename=ename; kind=kind; msg=msg; backtrace=bts} :: (snd cg).errors ]
  ;
  value add_exn cg loc ename (bts,exn) =
    let loc = match exn with [
          Ploc.Exc loc _ -> loc
        | _ -> loc
        ] in
    let msg = Printexc.to_string exn in
    (snd cg).errors := [ {loc=loc; ename=ename; kind="Fatal"; msg=msg; backtrace=bts} :: (snd cg).errors ]
  ;
  value add_failure cg loc ename s = add_error cg (loc, ename, "Fatal", s) ;
  value add_warning cg loc ename s = add_error cg (loc, ename, "Warning", s) ;
  value add_failuref cg loc ename fmt = Fmt.kstr (fun s -> add_error cg (loc, ename, "Fatal", s)) fmt ;
  value add_warningf cg loc ename fmt = Fmt.kstr (fun s -> add_error cg (loc, ename, "Warning", s)) fmt ;

  value set_alphabet cg l = (snd cg).gram_alphabet := l ;
  value alphabet cg = (snd cg).gram_alphabet ;

  value set_atn_first cg ename l = MHM.add (snd cg).atn_first (ename, l) ;
  value atn_first cg ename = MHM.map (snd cg).atn_first ename ;

  value set_atn_firstk cg ename l = MHM.add (snd cg).atn_firstk (ename, l) ;
  value atn_firstk cg ename = MHM.map (snd cg).atn_firstk ename ;

end ;
module CG = CompilingGrammar ;


module DebugCompile(S : sig value rexs : string ; value cg : CG.t; end) = struct
  open Print_gram ;
  open Llk_regexps ;
  value rexs = S.rexs ;
  value rex = rexs |> RT.pa_regexp_ast |> normalize_astre [] ;
  module C = Compile(struct value rex = rex ; value extra = (CG.alphabet S.cg); end) ;
end
;


module Anti = struct

(**

["flag"] for FLAG
["list"] for LIST0 and LIST1
["opt"] for OPT
["chr"] for CHAR
["flo"] for FLOAT
["int"] for INT
["int32"] for INT_l
["int64"] for INT_L
["nativeint"] for INT_n
["lid"] for LIDENT
["str"] for STRING
["uid"] for UIDENT
 *)
value infer_kinds cg loc s kinds =
  if kinds <> [] then kinds else
    match s with [
        ASflag _ _ _ -> ["flag"]
      | ASlist _ _ _ _ _ -> ["list"]
      | ASopt _ _ _ -> ["opt"]
      | AStok loc "CHAR" _ -> ["chr"]
      | AStok loc "FLOAT" _ -> ["flo"]
      | AStok loc "INT" _ -> ["int"]
      | AStok loc "INT_l" _ -> ["int32"]
      | AStok loc "INT_L" _ -> ["int64"]
      | AStok loc "INT_n" _ -> ["nativeint"]
      | AStok loc "LIDENT" _ -> ["lid"]
      | AStok loc "GIDENT" _ -> ["gid"]
      | AStok loc "STRING" _ -> ["str"]
      | AStok loc "UIDENT" _ -> ["uid"]
      | AStok loc "QUESTIONIDENT" _ -> ["?"]
      | AStok loc "QUESTIONIDENTCOLON" _ -> ["?:"]
      | AStok loc "TILDEIDENT" _ -> ["~"]
      | AStok loc "TILDEIDENTCOLON" _ -> ["~:"]
      | _ -> raise_failwithf (CG.adjust_loc cg loc) "cannot infer antiquotation kind for symbol %s" Pr.(symbol~{pctxt=errmsg} Pprintf.empty_pc s)
      ]
;

end
;

module S0Alphabet = struct
  value alphabet cg =
  let acc = ref [] in
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASkeyw _ kw as s -> do { Std.push acc (SPCL kw) ; s }
      | AStok _ cls tokopt as s -> do { Std.push acc (CLS cls tokopt) ; s }
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol } in do {
    List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) (CG.gram_entries cg) ;
    List.sort_uniq Llk_regexps.PatternBaseToken.compare acc.val
  }
;

value exec cg = do { CG.set_alphabet cg (alphabet cg) ; cg } ;
end ;

module S1ProcessRegexps = struct
open Llk_regexps ;

value process_regexps cg =
  let norm_res = List.fold_left (fun env (id, astre) ->
                  let re = normalize_astre env astre in
                  [(id,re)::env]
                ) [] (CG.gram_regexp_asts cg) in
  let norm_exts = List.fold_left (fun env (id, astre) ->
                  let re = normalize_astre env astre in
                  [(id,re)::env]
                ) [] (CG.gram_external_asts cg) in
  do {
    List.iter (CG.add_gram_regexp cg) norm_res ;
    List.iter (CG.add_gram_external cg) norm_exts ;
    cg
  }
;

value convert_regexp_references cg =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_psymbol = dt.migrate_a_psymbol in
  let migrate_a_psymbol dt = fun [
        {ap_symb=ASnterm loc nt [] None} as ps
           when CG.exists_regexp_ast cg nt ->
                {(ps) with ap_symb = ASregexp loc nt}
      | {ap_symb=ASnterm loc nt _ _}
           when not (CG.exists_entry cg nt || CG.exists_external_ast cg nt) ->
                raise_failwithf (CG.adjust_loc cg loc) "S1ProcessRegexps: no nonterminal %s found in grammar" (Name.print nt)
      | ps -> fallback_migrate_a_psymbol dt ps
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_psymbol = migrate_a_psymbol } in
  CG.withg cg {(CG.g cg) with gram_entries = List.map (dt.migrate_a_entry dt) (CG.gram_entries cg)}
;

value exec cg = cg |> process_regexps |> convert_regexp_references ;

end ;


module CheckSyntax = struct

value check cg =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm loc nt _ _
           when not (CG.exists_entry cg nt || CG.exists_external_ast cg nt) ->
                raise_failwithf (CG.adjust_loc cg loc) "CheckSyntax: no nonterminal %s defined in grammar" (Name.print nt)
      | ASnterm loc nt _ (Some _) when CG.exists_external_ast cg nt ->
                raise_failwithf (CG.adjust_loc cg loc) "CheckSyntax: external nonterminal %s has forbidden level marking" (Name.print nt)
      | ASregexp loc nt ->
         raise_failwithf (CG.adjust_loc cg loc) "CheckSyntax: regexp %s used in grammar in non-psymbol position" (Name.print nt)
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let fallback_migrate_a_psymbol = dt.migrate_a_psymbol in
  let migrate_a_psymbol dt = fun [
        {ap_symb=ASregexp loc nt} when not (CG.exists_regexp_ast cg nt) ->
            raise_failwithf (CG.adjust_loc cg loc) "CheckSyntax: no regexp %s defined in grammar" (Name.print nt)
      | {ap_symb=ASregexp _ _ } as ps -> ps
      | s -> fallback_migrate_a_psymbol dt s
      ] in
  let dt = { (dt) with
             Llk_migrate.migrate_a_symbol = migrate_a_symbol
           ; Llk_migrate.migrate_a_psymbol = migrate_a_psymbol
           } in
  List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) (CG.gram_entries cg)
;

value mentions cg =
  let entries = ref [] in
  let regexps = ref [] in
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm _ nt _ _ as s -> do { Std.push entries nt ; s }
      | ASregexp _ nt as s -> do { Std.push regexps nt ; s }
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with
             Llk_migrate.migrate_a_symbol = migrate_a_symbol
           } in do {
    List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) (CG.gram_entries cg) ;
    (entries.val, regexps.val)
  }
;

value free_names_of_regexp init re =
  let open Llk_migrate in
  let regexps = ref init in
  let dt = Llk_migrate.make_dt [] in
  let fallback_migrate_astre = dt.migrate_astre in
  let migrate_astre dt = fun [
        ID _ id as re when not (List.mem id dt.aux) -> do { Std.push regexps id ; re }
      | LETIN _ id re1 re2 as re -> do {
          ignore (dt.migrate_astre dt re1) ;
          ignore (dt.migrate_astre {(dt) with aux = [id :: dt.aux]} re2) ;
          re
        }
      | re -> fallback_migrate_astre dt re
      ] in
  let dt = { (dt) with
             Llk_migrate.migrate_astre = migrate_astre
           } in do {
    ignore (dt.migrate_astre dt re) ;
    List.sort_uniq Name.compare regexps.val
  }
;

value regexp_mentions cg = do {
    let acc = ref [] in
    (CG.gram_regexp_asts cg)
    |> List.iter (fun (id, re) -> do {
                    acc.val := acc.val @ (free_names_of_regexp [] re)
         }) ;
    List.sort_uniq Name.compare acc.val
  }
;

value check_names cg = do {
  let exported = (CG.g cg).gram_exports in
  let defined = (CG.gram_entries cg) |> List.map entry_name in
  let externals = (CG.gram_externals cg) |> List.map fst in
  let regexps = (CG.gram_regexp_asts cg) |> List.map fst in
  let multiply_defined = Std.intersect defined externals in
  if [] <> multiply_defined then
    Fmt.(failwithf "Entries are both external and defined: %a" (list ~{sep=sp} Name.pp) multiply_defined)
  else () ;
  let regexp_and_entry = Std.(intersect regexps (union defined externals)) in
  if [] <> regexp_and_entry then
    Fmt.(failwithf "Entries are both regexp and external/defined: %a" (list ~{sep=sp} Name.pp) regexp_and_entry)
  else () ;
  let missing = Std.(subtract exported (union defined externals)) in
  if [] <> missing then
    Fmt.(failwithf "Undefined exported entries: %a" (list ~{sep=sp} Name.pp) missing)
  else () ;
  let (mentioned_entries, mentioned_regexps) = mentions cg in
  let regexp_mentioned_regexps = regexp_mentions cg in
  let unused = Std.(subtract
                      defined
                      (union exported (union mentioned_entries (union mentioned_regexps regexp_mentioned_regexps)))) in
  if [] <> unused then
    Fmt.(failwithf "Unused entries: %a" (list ~{sep=sp} Name.pp) unused)
  else () 
  }
;

value exec x = do {
  check x ;
  check_names x ;
  x
}
;

end ;


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

value rec check_symbol cg env = fun [
    ASflag _ _ s -> check_symbol cg env s
  | ASkeyw _ _ -> ()
  | ASlist _ _ _ s None -> check_symbol cg env s
  | ASlist _ _ _ s (Some (s2, _)) -> do { check_symbol cg env s ; check_symbol cg env s2 }

  | ASnext _ _ -> ()
  | ASnterm _ _ _ _ -> ()
  | ASregexp _ _ -> ()
  | ASinfer _ _ -> ()
  | ASpriority _ _ -> ()
  | ASopt _ _ s -> check_symbol cg env s
  | ASleft_assoc _ _ s1 s2 _ ->  do { check_symbol cg env s1 ; check_symbol cg env s2 }
  | ASrules _ rs -> check_rules cg env rs
  | ASself _ _ -> ()
  | AStok _ _ _ -> ()
  | ASsyntactic _ s -> check_symbol cg env s
  | ASvala _ s _ -> check_symbol cg env s
  | ASanti _ _ -> ()
]

and check_rule cg env r =
  List.fold_left (fun env ps ->
      let patvars = match ps.ap_patt with [ None -> [] | Some p -> vars_of_patt p ] in do {
          patvars |> List.iter (fun v ->
            if Env.mem v env then
              raise_failwithf (CG.adjust_loc cg ps.ap_loc) "CheckLexical.check_rule: lexical hygiene violation on var %s" v
            else ()
          ) ;
          let env = Env.addl patvars env in
          check_symbol cg env ps.ap_symb ;
          env
      }
    ) env r.ar_psymbols

and check_rules cg env rl = List.iter (fun r -> ignore (check_rule cg env r)) rl.au_rules
;

value check_level cg env l = check_rules cg env l.al_rules ;

value check_levels cg env ll = List.iter (check_level cg env) ll ;

value check_entry cg e =
  check_levels cg (e.ae_formals |> List.concat_map vars_of_patt |> Env.mk) e.ae_levels ;

value exec cg = do { List.iter (check_entry cg) (CG.gram_entries cg) ; cg } ;

end ;

module S0ValaKinds = struct

value rec exec0 cg el =
  let open Llk_migrate in
  let dt = make_dt() in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASvala loc s kinds ->
        let anti_kinds = Anti.infer_kinds cg loc s kinds in
        ASvala loc (dt.migrate_a_symbol dt s) anti_kinds
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = {(dt) with migrate_a_symbol = migrate_a_symbol } in
  List.map (dt.migrate_a_entry dt) el
;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

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
module S2Coalesce = struct
  open Std ;

  value is_position_marked e = isSome e.ae_pos ;

  (** tsort entries by position, label.

      nodes: (entry, position option)
      edges:

        src: node with (e, Some pos)
        dst: node with (e, pos_opt') where e has a level with label [pos]

      edges for LEVEL, LIKE, AFTER, BEFORE, but NOT for FIRST, LAST
   *)

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
    
  type node = (Name.t * option a_position) ;
  value tsort_nodes (adj : list (node * list node)) =
    let adj = adj |> List.sort_uniq Stdlib.compare in
    Tsort.tsort (fun v l -> [v :: l]) adj [] ;

  value concat_entries = fun [
    [] -> assert False
  | [h::t] as el -> {(h) with ae_levels = List.concat_map (fun e -> e.ae_levels) el }
  ]
  ;

  value coalesce_entries_for cg ename el =
    let label2node =
      el
      |> List.concat_map (fun e ->
             e
             |> entry_labels
             |> List.map (fun lab -> (lab, entry2node e))
           ) in do {
    match el |> List.map entry_position |> List.find_all ((=) None) with [
        [] -> failwith Fmt.(str "construct_graph: NO entry named %s is position-free" (Name.print ename))
      | [_] -> ()
      | l -> failwith Fmt.(str "construct_graph: exactly one entry named %s MUST be position-free:\n%a"
                           (Name.print ename)
                        (list string)
                        (el |> List.map entry_location |> List.map (CG.adjust_loc cg) |> List.map Ploc.string_of_location)
           )
      ] ;
    if not (distinct (el |> List.concat_map entry_labels)) then
      failwith Fmt.(str "construct_graph: entry %s does not have distinct labels" (Name.print ename))
    else () ;

    let adj = el |> List.filter_map (fun e ->
      match entry_position e with [
          Some(POS_LEVEL lev | POS_AFTER lev | POS_BEFORE lev) ->
          (match List.assoc lev label2node with [
               exception Not_found ->
                         failwith Fmt.(str "construct_graph: entry %s, position LEVEL \"%s\" not found"
                                         (Name.print (entry_name e)) lev)
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
(*
    let sorted_el = List.map concat_entries sorted_ell in
 *)
    let sorted_el = List.concat sorted_ell in
    let (e0, el) = match sorted_el with [
          [] -> assert False
        | [e0::el] when entry_position e0 <> None -> assert False
        | [e0::el] -> (e0, el)
        ] in
    List.fold_left insert1 e0 el
  }
  ;

  value coalesce_entries cg el =
    let all_entry_names =
      el |> List.map entry_name |> List.sort_uniq Name.compare in
    all_entry_names
    |> List.map (fun name ->
      let el = el |> List.find_all (fun e -> name = entry_name e) in
      match el with [
          [({ae_pos = None} as e)] -> e
        | [{ae_pos = Some _}] ->
           failwith Fmt.(str "construct_graph: only one entry named %s, but with position" (Name.print name))
        | el -> coalesce_entries_for cg name el
         ])
  ;

  value exec cg = CG.withg cg {(CG.g cg) with gram_entries = coalesce_entries cg (CG.gram_entries cg)} ;

end ;

module CheckNoPosition = struct

value exec (({gram_entries=el}, _) as cg) = do {
  el |> List.iter (fun e ->
      if e.ae_pos <> None then
        raise_failwithf (CG.adjust_loc cg e.ae_loc) "CheckNoPosition: entry %s still has a position" (Name.print e.ae_name)
      else ()
    ) ;
  cg
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

type key_t = [ NT of Name.t and option string | NEXT | SELF ] ;

value lookup_rho s rho : Name.t = List.assoc s rho ;

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

value rec formals2actuals cg l = List.map (f2a cg) l
and f2a cg = fun [
      <:patt:< $lid:id$ >> -> <:expr< $lid:id$ >>
    | <:patt:< ( $list:l$ ) >> -> <:expr< ( $list:formals2actuals cg l$ ) >>
    | <:patt:< ( $p$ : $t$ ) >> -> <:expr< ( $f2a cg p$ : $t$ ) >>
    | <:patt:< () >> -> <:expr< () >>
    | p ->
       raise_failwithf (CG.adjust_loc cg (loc_of_patt p)) "formals2actuals: malformed formal"
    ]
;

module S3Precedence = struct 

value rewrite_righta cg loc (ename,eformals) ~{cur} ~{next} rho rl =
  let right_rho = Subst.[
        (SELF, cur)
       ;(NT ename None, cur)
    ] in
  let lid_guess =
    match List.hd rl with [
        {ar_psymbols=[{ap_patt= Some <:patt< $lid:v$ >>; ap_symb=ASself _ _} :: _]} -> v
      | {ar_psymbols=[{ap_patt= Some <:patt< $lid:v$ >>; ap_symb=ASnterm _ nt _ None} :: _]} when ename = nt -> v
      | _ -> "x"
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
                                   ap_patt = Some <:patt< $lid:lid_guess$ >> ;
                                   ap_symb = ASnterm loc next (formals2actuals cg eformals) None}];
                   ar_action = Some <:expr< $lid:lid_guess$ >> } in
  rl @ [last_rule]
;

value rewrite_lefta loc ename ~{cur} ~{next} ~{greedy} rho rl =
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
    ASleft_assoc loc greedy left_symbol
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

value rewrite1 cg e (ename, eargs) ~{cur} ~{next} dict l = do {
    let loc = l.al_loc in
    let l =
      if ([] = l.al_rules.au_rules) then
        {(l) with al_label = None ; al_assoc = None }
      else
      match l.al_assoc with [
          None | Some NONA ->
            let rules =
              l.al_rules.au_rules
              |> Subst.rules Subst.[
                     (SELF, cur)
                    ;(NEXT, next)
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
               raise_failwithf (CG.adjust_loc cg l.al_rules.au_loc) "rewrite1: entry %s RIGHTA level rules must all have at least 2 psymbols"
                 (Name.print ename)
             else () ;
             let last_symbol = 
               let (last_psymbol, _) = Std.sep_last (List.hd rl).ar_psymbols in
               last_psymbol.ap_symb in
             if not (rl |> List.for_all (fun r -> 
                               equal_a_symbol last_symbol (fst (Std.sep_last r.ar_psymbols)).ap_symb)) then
               raise_failwithf (CG.adjust_loc cg l.al_rules.au_loc) "rewrite1: entry %s RIGHTA level does not have identical last symbols\n%s"
                 (Name.print ename)
                 Pr.(entry ~{pctxt=errmsg} Pprintf.empty_pc e)
             else () ;
             match last_symbol with [
                 ASnterm _ name _ None when name = ename -> ()
               | ASself _ _ -> ()
               | s -> raise_failwithf (CG.adjust_loc cg (loc_of_a_symbol s)) "rewrite1: entry %s RIGHTA level has last psymbol non-recursive" (Name.print ename)
               ] ;
             let rl = rewrite_righta cg loc (ename,eargs) ~{cur=cur} ~{next=next} Subst.[
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

          | Some (LEFTA greedy) ->
             let rl = l.al_rules.au_rules in do {
             if rl |> List.exists (fun r -> List.length r.ar_psymbols < 2) then
               raise_failwithf (CG.adjust_loc cg l.al_rules.au_loc) "rewrite1: entry %s LEFTA level rules must all have at least 2 psymbols"
                 (Name.print ename)
             else () ;
             let first_symbol =
               let first_psymbol = List.hd (List.hd rl).ar_psymbols in
               first_psymbol.ap_symb in
             rl |> List.iter (fun r ->
                       if not (equal_a_symbol first_symbol (List.hd r.ar_psymbols).ap_symb) then
                         raise_failwithf (CG.adjust_loc cg r.ar_loc) "rewrite1: entry %s LEFTA level does not have identical first symbols"
                           (Name.print ename)
                       else ()
                     ) ;
             match first_symbol with [
                 ASnterm _ name _ None when name = ename -> ()
               | ASself _ _ -> ()
               | _ -> raise_failwithf (CG.adjust_loc cg l.al_rules.au_loc) "rewrite1: entry %s LEFTA level has first psymbol non-recursive"
                        (Name.print ename)
               ] ;
             let rl = rewrite_lefta loc ename ~{cur=cur} ~{next=next} ~{greedy=greedy} Subst.[
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

value passthru_entry cg e from_name to_name =
  let loc = e.ae_loc in
  let formals = e.ae_formals in
  let actuals = formals2actuals cg e.ae_formals in
  {ae_loc = loc; ae_name = from_name; ae_formals = formals ; ae_pos = None;
   ae_preceding_psymbols = [];
   ae_source_symbol = None;
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


value exec1 cg e = do {
  assert (e.ae_pos = None) ;
  let ename = e.ae_name in
  let formals = e.ae_formals in
  let levels = e.ae_levels in
  let n_levels = List.length levels in
  let zero_name = CG.fresh_name cg e.ae_name in
  let named_levels =
    List.mapi (fun i l -> (i+1, CG.fresh_name cg e.ae_name, l)) levels in
  let first_name = Std.snd3 (List.hd named_levels) in
  let bot_name = CG.fresh_name cg e.ae_name in
  let i2name = [(0,zero_name)]@(List.map (fun (i, n, _) -> (i,n)) named_levels)@[(n_levels+1, bot_name)] in
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
           let next_name = match List.assoc (i+1) i2name with [
                 x -> x
               | exception Not_found -> assert False ] in
           rewrite1 cg e (ename,formals) ~{cur=newname} ~{next=next_name} dict l) in
  let top2_entries = [
      passthru_entry cg e e.ae_name zero_name ;
      passthru_entry cg e zero_name first_name
    ] in
  let bottom_entries = [
      passthru_entry cg e bot_name zero_name
    ] in

  (dict, top2_entries @ newents @ bottom_entries)
}
;

value substitute_self e =
  Subst.entry Subst.[(SELF, e.ae_name)] e
;

value exec0 cg e =
  match e.ae_levels with [
      [] -> ([], [{ (e) with ae_pos = None }])
    | [l] ->
       (match l.al_assoc with [
            Some a ->
            raise_failwithf (CG.adjust_loc cg l.al_loc) "S3Precedence(%s): associativity marking on single-level entry: %s"
              (Name.print e.ae_name) (Pr.assoc Pprintf.empty_pc a)
          | None ->
             ([], [substitute_self { (e) with ae_pos = None ; ae_levels = [{ (l) with al_label = None }]}])
       ])
    | _ -> exec1 cg e
    ]
;

value exec cg =
  let pl = List.map (exec0 cg) (CG.gram_entries cg) in
  let dict = pl |> List.concat_map fst in
  let el = List.concat_map snd pl in
  let el = List.map (Subst.entry dict) el in
  CG.withg cg {(CG.g cg) with gram_entries = el }
;

end ;

module CheckNoLabelAssocLevel = struct

value check_no_level cg el =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm loc nt _ (Some _) when CG.exists_external_ast cg nt ->
        raise_failwithf (CG.adjust_loc cg loc) "CheckNoLabelAssocLevel: level marking found on EXTERNAL nonterminal %s" (Name.print nt)
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol } in
  List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) el
;

value exec (({gram_entries=el}, _) as cg) = do {
  check_no_level cg el ;
  el |> List.iter (fun e ->
    e.ae_levels |> List.iter (fun l -> do {
      match l.al_label with [
          None -> ()
        | Some lab ->
           raise_failwithf (CG.adjust_loc cg e.ae_loc) "CheckNoLabelAssocLevel: entry %s still has a label %s" (Name.print e.ae_name) lab
        ] ;
      match l.al_assoc with [
          None -> ()
        | Some a ->
           raise_failwithf (CG.adjust_loc cg e.ae_loc) "CheckNoLabelAssocLevel: entry %s still has an assoc %a" (Name.print e.ae_name) pp_a_assoc a
        ]
    })
  ) ;
  cg
}
;

end ;

module CheckNoSelfNext = struct

value check_no_self_next cg e =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASself loc _ | ASnext loc _ ->
          raise_failwithf (CG.adjust_loc cg loc) "CheckNoSelfNext(%s): internal error: leftover SELF/NEXT found" (Name.print e.ae_name)

      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol } in
  ignore (dt.migrate_a_entry dt e)
;

value exec (({gram_entries=el}, _) as cg) = do {
  List.iter (check_no_self_next cg) el ;
  cg
}
;

end ;

module S5LeftFactorize = struct

value extract_left_factors1 rl =
  if List.length rl > 1 &&
       rl |> List.for_all (fun r -> List.length r.ar_psymbols > 0) &&
         (let left_psymbol = List.hd (List.hd rl).ar_psymbols in
          rl |> List.for_all (fun r -> equal_a_psymbol left_psymbol (List.hd r.ar_psymbols))) then
    let left_psymbol = List.hd (List.hd rl).ar_psymbols in
    match left_psymbol with [
        {ap_symb=ASinfer _ _} -> ([], rl)
      | _ ->
         ([left_psymbol],
          rl |> List.map (fun r -> {(r) with ar_psymbols = List.tl r.ar_psymbols }))
      ]
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

value rec left_factorize0 cg loc rl =
  match extract_left_factors rl with [
      ([], rl) -> rl
    | (factors,rl) ->
       let n = CG.fresh_name cg (Name.mk "x") in
       let right_psymb = {
           ap_loc = loc
         ; ap_patt = Some <:patt< $lid:Name.print n$ >>
         ; ap_symb = ASrules loc { au_loc = loc ; au_rules = (left_factorize cg loc rl) }
         } in
       [{ ar_loc = loc
        ; ar_psymbols = factors @ [ right_psymb ]
        ; ar_action = Some <:expr< $lid:Name.print n$ >> }]
    ]

and left_factorize cg loc rl =
  let mt_rules = List.filter (fun r -> [] = r.ar_psymbols) rl in
  let nonmt_rules = List.filter (fun r -> [] <> r.ar_psymbols) rl in
  let head_psymbols = List.map (fun r -> List.hd r.ar_psymbols) nonmt_rules in
  let head_psymbols = List.sort_uniq compare_a_psymbol head_psymbols in
  let partitions =
    head_psymbols
    |> List.map (fun ps ->
           nonmt_rules |> List.filter (fun r -> equal_a_psymbol ps (List.hd r.ar_psymbols))) in
  List.concat ((List.map (left_factorize0 cg loc) partitions) @ [mt_rules])
;

value make_dt cg =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_rules = dt.migrate_a_rules in
  let migrate_a_rules dt rs = 
    let rs = fallback_migrate_a_rules dt rs in
    let loc = rs.au_loc in    
    {(rs) with au_rules = left_factorize cg loc rs.au_rules }
  in

  { (dt) with Llk_migrate.migrate_a_rules = migrate_a_rules }
;

value left_factorize_level cg l =
  let dt = make_dt cg in
  dt.migrate_a_level dt l
;

value left_factorize_levels cg l = do {
  assert (1 = List.length l) ;
  List.map (left_factorize_level cg) l
}
;

value exec0 cg e = {(e) with ae_levels = left_factorize_levels cg e.ae_levels } ;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = List.map (exec0 cg) (CG.gram_entries cg)} ;

end ;

module First = struct

exception ExternalEntry of Name.t ;

value rec psymbols cg = fun [
  [] -> TS.mk [None]
| [{ap_symb=ASregexp _ _} :: t] -> psymbols cg t
| [{ap_symb=ASinfer _ _} :: t] -> psymbols cg t
| [{ap_symb=ASpriority _ _} :: t] -> psymbols cg t
| [{ap_symb=ASsyntactic _ _} :: t] -> psymbols cg t
| [h::t] ->
   let fh = psymbol cg h in
   if TS.mem None fh then
     TS.(union (except None fh) (psymbols cg t))
   else fh
]

and psymbol cg ps = symbol cg ps.ap_symb

and symbol cg = fun [
      ASflag _ _ s -> TS.(union (symbol cg s) (mk[None]))
    | ASkeyw _ kw -> TS.mk [Some (SPCL kw)]
    | (ASlist loc _ lml elem_s sepb_opt) as s ->
       let felem = symbol cg elem_s in
       if TS.mem None felem then
         raise_failwithf (CG.adjust_loc cg loc) "First.symbol: LIST element MUST NOT be nullable: %s" Pr.(symbol~{pctxt=errmsg} Pprintf.empty_pc s)
       else 
         match (lml, sepb_opt) with [
             (LML_1, None) -> felem
           | (LML_1, _) -> felem
           | (LML_0, _) -> TS.(union felem (mk [None]))
           ]

    | ASnext _ _ -> assert False

    | ASnterm _ nt _ _ when CG.exists_entry cg nt -> CG.first cg nt
    | ASnterm _ nt _ _ when CG.exists_external_ast cg nt ->
     let rex = CG.gram_external cg nt in
     let module C = Compile(struct value rex = rex ; value extra = (CG.alphabet cg); end) in
     let is_nullable = C.BEval.nullable rex in
     let nulls = if is_nullable then [None] else [] in
     let toks = List.map (fun x -> Some x) (C.BEval.OutputDfa.first_tokens rex) in
     TS.mk (toks@nulls)

    | ASopt _ _ s -> TS.(union (mk [None]) (symbol cg s))

  | ASleft_assoc _ _ s1 s2 _ ->
     let fs1 = symbol cg s1 in
     if not (TS.mem None fs1) then fs1
     else TS.(union (except None fs1) (symbol cg s2))

  | ASrules _ rl -> rules cg rl
  | ASself _ _ -> assert False
  | AStok _ cls tokopt -> TS.mk[Some (CLS cls tokopt)]
  | ASvala loc s anti_kinds ->
     TS.(union (symbol cg s) (anti_kinds |> List.concat_map (fun s -> [Some (ANTI s); Some (ANTI ("_"^s))]) |> mk))
  | ASanti loc anti_kinds ->
     TS.(anti_kinds |> List.concat_map (fun s -> [Some (ANTI s); Some (ANTI ("_"^s))]) |> mk)
  | ASregexp loc _ as s ->
     raise_failwithf (CG.adjust_loc cg loc) "First.symbol: internal error: unrecognized %a" pp_a_symbol s
  | ASinfer loc _ as s ->
     raise_failwithf (CG.adjust_loc cg loc) "First.symbol: internal error: unrecognized %a" pp_a_symbol s
  | ASpriority loc _ as s ->
     raise_failwithf (CG.adjust_loc cg loc) "First.symbol: internal error: unrecognized %a" pp_a_symbol s
  | ASsyntactic loc _ as s ->
     raise_failwithf (CG.adjust_loc cg loc) "First.symbol: internal error: unrecognized %a" pp_a_symbol s
]

and rule cg r = psymbols cg r.ar_psymbols

and rules cg l =
  let rules = l.au_rules in
  TS.unionl (List.map (rule cg) rules)
;

value level cg l = rules cg l.al_rules ;

value comp1_entry cg e =
try
  let fi =
    e.ae_levels
    |> List.map (level cg)
    |> TS.unionl in
  CG.add_first cg e.ae_name fi
with ExternalEntry _ -> ()
;

value comp1 el cg = List.iter (comp1_entry cg) el ;

value rec comprec cg el = do {
  let m0 = CG.firstmap cg in
  comp1 el cg ;
  let m1 = CG.firstmap cg in
  if m0 = m1 then cg else comprec cg el
}
;

value exec0 cg el = comprec cg el ;
value exec cg = exec0 cg (CG.gram_entries cg) ;

end ;

module Follow = struct

value nullable l = TS.mem None l ;

(** [fifo_concat ~{must} ~{if_nullable} fi fo]

    when must is true: concat fi.fo, removing eps if present.

    when must is false:

    when if_nullable is true, concats fi.fo IF fi is nullable.

    when if_nullable is false, checks that fi is NOT nullable, and concats.

 *)
value fifo_concat cg loc ?{must=False} ?{if_nullable=False} fi fo =
  match (must, if_nullable, nullable fi) with [
      (True, True, _) ->
      raise_failwithf (CG.adjust_loc cg loc) "fifo_concat: incompatible arguments with must=True, if_nullable=True"
    | (_, True, True) -> TS.(union (map Std.outSome (TS.except None fi)) fo)
    | (_, True, False) -> TS.map Std.outSome fi
    | (_, False, True) ->
       raise_failwithf (CG.adjust_loc cg loc) "fifo_concat: [fi] is nullable, but if_nullable=False"
    | (_, False, False) -> TS.(union (TS.map Std.outSome fi) fo)
    ]
;

value fi2fo cg loc fi = fifo_concat cg loc ~{must=True} fi TS.mt ;

(** Compute "FI-FO" First(s).[Follow(s) when first contains epsilon].

    We pass:

    fimap: map for computing FIRST
    mm: the current mutable map of FOLLOW
    ff: "full follow" of whatever might follow the current symbol

    Procedure:

    We invoke fifo on all sub-symbols.  When invoked on a nonterminal, we
    add "full follow" to the FOLLOW set of the nonterminal.

 *)

value watch_follow (nt : Name.t) (ff : TS.t token) = () ;


value rec fifo_psymbols cg e ff = fun [
      [] -> ff
    | [{ap_symb=ASregexp _ _} :: t] -> fifo_psymbols cg e ff t
    | [{ap_symb=ASinfer _ _} :: t] -> fifo_psymbols cg e ff t
    | [{ap_symb=ASpriority _ _} :: t] -> fifo_psymbols cg e ff t
    | [{ap_symb=ASsyntactic _ _} :: t] -> fifo_psymbols cg e ff t
    | [h::t] ->
       let ft = fifo_psymbols cg e ff t in
       fifo_psymbol cg e ft h
       
]

and fifo_psymbol cg e ff ps =
  fifo_symbol cg e ff ps.ap_symb

(** [fifo_symbol cg e ff]

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

and fifo_symbol cg e ff = fun [
      ASflag loc _ s | ASopt loc _ s ->
      (* the fifo of [FLAG s] is always the concat of the FIRST of s
         (minus eps) and the full-follow of [FLAG s], since [FLAG s]
         is nullable.
       *)
      let _ = fifo_symbol cg e ff s in
      let fi_s = First.symbol cg s in do {
        if nullable fi_s then
          raise_failwith (CG.adjust_loc cg loc) "FLAG/OPT must not be nullable"
        else
          fifo_concat cg ~{must=True} loc fi_s ff
      }

    | ASkeyw _ kw -> TS.mk[(SPCL kw)]

    | ASlist loc _ lml s sepopt_opt ->
       (* A. if a LIST has element that is NOT nullable, OR is LIST0,
          then the fifo is just the firsts of that element.

          B. if the element is nullable, then combine fifo_element,
          fifo_sep (if any) and full-follow

          Procedure: by cases:
           
          0. call [ff] argument "full-follow"
        *)

       let fi_s = First.symbol cg s in
       if nullable fi_s then
         raise_failwithf (CG.adjust_loc cg loc) "LIST element must not be nullable"
       else
       match (lml, sepopt_opt) with [
           (*
             1. LIST1, no SEP:

                a. fifo is [FIRST s].{if_nullable}.full-follow
                b. compute [FIFO s] with ff=[FIRST s].full-follow
            *)

           (LML_1, None) ->

           let _ = 
             let ff = fifo_concat cg loc ~{must=True} fi_s ff in
             fifo_symbol cg e ff s in

           fifo_concat cg loc ~{if_nullable=True} fi_s ff

         (*
           2. LIST1, mandatory SEP s2:

             a. fifo is [FIRST s].{if_nullable}.(([FIRST s2].[]) union full-follow)
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.([FIRST s2].full-follow)
          *)

         | (LML_1, Some (s2, False)) ->
           let fi_s2 = First.symbol cg s2 in
           if nullable fi_s2 then
             raise_failwithf (CG.adjust_loc cg loc) "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s2 (fi2fo cg loc fi_s)) ff) in
             fifo_symbol cg e ff s in

           let _ =
             let ff = (fifo_concat cg loc ~{if_nullable=True} fi_s (fifo_concat cg loc fi_s2 ff)) in
             fifo_symbol cg e ff s2 in

           fifo_concat cg loc ~{if_nullable=True} fi_s (TS.union (fi2fo cg loc fi_s2) ff)

         (*

          2'. LIST1, optional last SEP s2:

             a. fifo is [FIRST s].{if_nullable}.([FIRST s2] union full-follow)
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.[FIRST s2] union full-follow
          *)

         | (LML_1, Some (s2, True)) ->
           let fi_s2 = First.symbol cg s2 in
           if nullable fi_s2 then
             raise_failwithf (CG.adjust_loc cg loc) "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s2 (fi2fo cg loc fi_s)) ff) in
             fifo_symbol cg e ff s in

           let _ =
             let ff = TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s (fi2fo cg loc fi_s2)) ff) in
             fifo_symbol cg e ff s2 in

           fifo_concat cg loc ~{if_nullable=True} fi_s (TS.union (fi2fo cg loc fi_s2) ff)

         (*
          3. LIST0, no SEP:

             a. fifo is [FIRST s].full-follow
             b. compute [FIFO s] with ff=[FIRST s].full-follow
          *)

         | (LML_0, None) ->
           let _ = 
             let ff = fifo_concat cg loc ~{must=True} fi_s ff in
             fifo_symbol cg e ff s in

           fifo_concat cg loc ~{must=True} fi_s ff

         (*
          4. LIST0, mandatory SEP s2:

             a. fifo is [FIRST s].{if_nullable}.([FIRST s2].[]) union full-follow
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.[FIRST s2]
          *)

         | (LML_0, Some (s2, False)) ->
           let fi_s2 = First.symbol cg s2 in
           if nullable fi_s2 then
             raise_failwithf (CG.adjust_loc cg loc) "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s2 (fi2fo cg loc fi_s)) ff) in
             fifo_symbol cg e ff s in

           let _ =
             let ff = (fifo_concat cg loc ~{if_nullable=True} fi_s (fifo_concat cg loc fi_s2 ff)) in
             fifo_symbol cg e ff s2 in

           TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s (fi2fo cg loc fi_s2)) ff)

         (*
          4. LIST0, optional last SEP s2:

             a. fifo is [FIRST s].{if_nullable}.([FIRST s2].[]) union full-follow
             b. compute [FIFO s] with ff=([FIRST s2].{if_nullable}.[FIRST s]) union full-follow
             c. compute [FIFO s2] with ff=[FIRST s].{if_nullable}.[FIRST s2] union full-follow
          *)

         | (LML_0, Some (s2, True)) ->
           let fi_s2 = First.symbol cg s2 in
           if nullable fi_s2 then
             raise_failwithf (CG.adjust_loc cg loc) "LIST separator must not be nullable"
           else

           let _ =
             let ff = TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s2 (fi2fo cg loc fi_s)) ff) in
             fifo_symbol cg e ff s in

           let _ =
             let ff = TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s (fi2fo cg loc fi_s2)) ff) in
             fifo_symbol cg e ff s2 in

           TS.(union (fifo_concat cg loc ~{if_nullable=True} fi_s (fi2fo cg loc fi_s2)) ff)

         ]

  | ASnext loc _ | ASself loc _ -> raise_failwithf (CG.adjust_loc cg loc) "fifo_symbol: internal error: NEXT should not occur here"
  | ASnterm loc nt _ _ as s when CG.exists_entry cg nt -> do {
        watch_follow nt ff ;
        CG.add_follow cg ~{from=Name.print e.ae_name} nt ff ;
        let fi_s = First.symbol cg s in
        fifo_concat cg loc ~{if_nullable=True} fi_s ff
      }

  | ASnterm loc nt _ _ as s when CG.exists_external_ast cg nt ->
     let rex = CG.gram_external cg nt in
     let module C = Compile(struct value rex = rex ; value extra = (CG.alphabet cg); end) in
     C.BEval.OutputDfa.first_tokens rex

  | ASleft_assoc loc _ s1 s2 _ ->
  (* 1. fifo is [FIRST s1].{is_nullable}.[FIRST s2].{is_nullable}.full-follow
     2. compute [FIFO s1] with ff=[FIRST s2] union full-follow
     3. compute [FIFO s2] with ff=[FIRST s2].{is_nullable}.full-follow
   *)                               
     let fi_s1 = First.symbol cg s1 in
     let fi_s2 = First.symbol cg s2 in

     let _ =
       let ff = TS.(union (fi2fo cg loc fi_s2) ff) in
       fifo_symbol cg e ff s1 in

     let _ =
       let ff = TS.(union (fi2fo cg loc fi_s2) ff) in
       fifo_symbol cg e ff s2 in

     fifo_concat cg loc ~{if_nullable=True} fi_s1
       (fifo_concat cg loc ~{if_nullable=True} fi_s2 ff)

  | ASrules loc rs ->
     fifo_rules cg e ff rs

  | AStok loc cls tokopt -> TS.mk [CLS cls tokopt]

  | ASvala loc s sl as s0 ->
     let _ = fifo_symbol cg e ff s in

     let fi_vala = First.symbol cg s0 in
     fifo_concat cg loc ~{if_nullable=True} fi_vala ff

  | ASanti loc sl as s0 ->
     let fi_vala = First.symbol cg s0 in
     fifo_concat cg loc ~{if_nullable=True} fi_vala ff

  | s -> raise_failwithf (CG.adjust_loc cg (loc_of_a_symbol s)) "fifo_symbol: %s" Pr.(symbol~{pctxt=errmsg} Pprintf.empty_pc s)
]

and fifo_rule cg e ff r =
  fifo_psymbols cg e ff r.ar_psymbols

and fifo_rules cg e ff rs =
  let loc = rs.au_loc in
  let rl = rs.au_rules in
  let fi_rs = rl |> List.map (First.rule cg) |> TS.unionl in do {
    rl |> List.iter (fun r ->
              ignore (fifo_rule cg e ff r)) ;
    fifo_concat cg loc ~{if_nullable=True} fi_rs ff
  }

and fifo_level cg e ff lev =
  fifo_rules  cg e ff lev.al_rules
;

value comp1_entry cg e =
try
  let ll = e.ae_levels in do {
  assert (1 = List.length ll) ;
  let e_ff = CG.follow cg e.ae_name in
  ignore (fifo_level cg e e_ff (List.hd ll))
}
with First.ExternalEntry _ -> ()
;
  

value comp1 cg el =
  List.iter (comp1_entry cg) el ;

value rec comprec el cg = do {
  let m0 = CG.followmap cg in
  comp1 cg el ;
  let m1 = CG.followmap cg in
  if m0 = m1 then cg else comprec el cg ;
}
;

value exec0 cg ~{tops} el = do {
  ignore (First.exec0 cg el) ;
  tops |> List.iter (fun t ->
              CG.add_follow cg ~{from="entrypoint"} t [CLS "EOI" None]) ;
  comprec el cg
}
;

value exec1 ~{tops} cg = exec0 cg ~{tops=tops} (CG.gram_entries cg) ;

value exec (({gram_loc=loc; gram_exports=expl; gram_entries=el; gram_id=gid}, _) as cg) = do {
  exec0 cg ~{tops=expl} el ;
  cg
}
;

end ;

module FreeLids = struct

value free_lids_of_expr e =
  let acc = ref [] in
  let pushid id = Std.push acc id in
  let dt = Llk_migrate.Camlp5.make_dt () in
  let fallback_migrate_expr = dt.migrate_expr in
  let migrate_expr dt e = do {
    match e with [
        <:expr< $lid:x$ >> -> pushid x
      | _ -> ()
      ] ;
      fallback_migrate_expr dt e
  } in
  let dt = { (dt) with migrate_expr = migrate_expr } in do {
    ignore (dt.migrate_expr dt e) ;
    acc.val |> List.sort_uniq Stdlib.compare
  }
;

value free_lids_of_patt e =
  let acc = ref [] in
  let pushid id = Std.push acc id in
  let dt = Llk_migrate.Camlp5.make_dt () in
  let fallback_migrate_patt = dt.migrate_patt in
  let migrate_patt dt e = do {
    match e with [
        <:patt< $lid:x$ >> -> pushid x
      | _ -> ()
      ] ;
      fallback_migrate_patt dt e
  } in
  let dt = { (dt) with migrate_patt = migrate_patt } in do {
    ignore (dt.migrate_patt dt e) ;
    acc.val |> List.sort_uniq Stdlib.compare
  }
;

value free_lids_of =
  let acc = ref [] in
  let pushe e =
    e |> free_lids_of_expr |> List.iter (Std.push acc) in
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let fallback_migrate_a_rule = dt.migrate_a_rule in
  let migrate_a_symbol dt s = 
    do { match s with [
             ASleft_assoc _ _ _ _ e -> pushe e
           | ASself _ el -> List.iter pushe el
           | ASnext _ el -> List.iter pushe el
           | ASnterm _ _ el _ -> List.iter pushe el
           | _ -> ()
           ];
         fallback_migrate_a_symbol dt s
       } in
  let migrate_a_rule dt r = do {
    match r.ar_action with [
        None -> () | Some e -> pushe e
      ] ;
    fallback_migrate_a_rule dt r
  } in
  let dt = { (dt) with migrate_a_rule = migrate_a_rule
                     ; migrate_a_symbol = migrate_a_symbol } in
  let of_a_rules rs = do {
    acc.val := [] ;
    ignore (dt.migrate_a_rules dt rs) ;
    acc.val |> List.sort_uniq Stdlib.compare
  } in
  let of_a_symbol s = do {
    acc.val := [] ;
    ignore (dt.migrate_a_symbol dt s) ;
    acc.val |> List.sort_uniq Stdlib.compare
  } in
  (of_a_rules, of_a_symbol)
;

  value free_lids_of_a_rules = (fst free_lids_of) ;
  value free_lids_of_a_symbol = (snd free_lids_of) ;

end ;

module S6LambdaLift = struct
  (** in each entry, replace all multi-way rules with a new entry;
      repeat until there are no multi-way rules left in any entry.
   *)

open FreeLids ;

value rec lift_rules cg acc e0 left_psyms rl = { (rl) with au_rules = List.map (lift_rule cg acc e0 left_psyms) rl.au_rules }

and lift_rule cg acc e0 left_psyms r =
  let (_, revps, left_psyms) = List.fold_left (fun (stkpat, revps, left_psyms) ps ->
    let ps = lift_psymbol cg acc e0 left_psyms stkpat ps in
    let stkpat = match ps.ap_patt with [ None -> stkpat | Some p -> [p :: stkpat] ] in
    (stkpat, [ps :: revps], left_psyms@[ps])
  ) ([], [], []) r.ar_psymbols in
  { (r) with ar_psymbols = List.rev revps }

and lift_psymbol cg acc e0 left_psyms stkpat ps =
  { (ps) with ap_symb = lift_symbol cg acc e0 left_psyms stkpat ps.ap_symb }

and lift_symbol cg acc e0 left_psyms revpats = fun [
    ASflag loc g s -> ASflag loc g (lift_symbol cg acc e0 [] revpats s)
  | ASkeyw _ _ as s -> s
  | ASanti _ _ as s -> s

  | ASlist loc g lml s None ->
     ASlist loc g lml (lift_symbol cg acc e0 [] revpats s) None
  | ASlist loc g lml s (Some (s2, b)) ->
     ASlist loc g lml (lift_symbol cg acc e0 [] revpats s) (Some (lift_symbol cg acc e0 [] revpats s2, b))

  | ASnext _ _ as s -> s
  | ASnterm _ _ _ _ as s -> s
  | ASregexp _ _ as s -> s
  | ASinfer _ _ as s -> s
  | ASpriority _ _ as s -> s
  | ASopt loc g s -> ASopt loc g (lift_symbol cg acc e0 [] revpats s)

  | ASleft_assoc loc g s1 s2 e ->
     ASleft_assoc loc g (lift_symbol cg acc e0 [] revpats s1) (lift_symbol cg acc e0 [] revpats s2) e

  | ASrules loc rl as s ->
     let formals = e0.ae_formals @ (List.rev revpats) in
     let ids_of_rl = free_lids_of_a_rules rl in
     let formals =
       formals
     |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) ids_of_rl) in
     let actuals = formals2actuals cg formals in
     let new_ename = CG.fresh_name cg e0.ae_name in do {
       let new_e = {
         ae_loc = rl.au_loc
       ; ae_name = new_ename
       ; ae_pos = None
       ; ae_formals = formals
       ; ae_levels = [{al_loc = rl.au_loc; al_label = None ; al_assoc = None ; al_rules = rl}]
       ; ae_preceding_psymbols = left_psyms
       ; ae_source_symbol = Some s
       } in do {
         Std.push acc new_e ;
         ASnterm rl.au_loc new_ename actuals None
       }
     }

  | ASself _ _ as s -> s
  | AStok _ _ _ as s -> s
  | ASsyntactic loc s -> ASsyntactic loc (lift_symbol cg acc e0 left_psyms revpats s)
  | ASvala loc s sl -> ASvala loc (lift_symbol cg acc e0 left_psyms revpats s) sl
]
;

value lift_level cg acc e0 left_psyms l = { (l) with al_rules = lift_rules cg acc e0 left_psyms l.al_rules } ;

value lift_levels cg acc e0 ll = do {
    assert (1 = List.length ll) ;
    let left_psyms = e0.ae_preceding_psymbols in
    List.map (lift_level cg acc e0 left_psyms) ll
}    
;
value lift_entry cg acc e =
  let ll = lift_levels cg acc e e.ae_levels in
  { (e) with ae_levels = ll }
;
  
value exec0 cg el =
  let rec erec el =
    let acc = ref [] in
    let el = List.map (lift_entry cg acc) el in
    if [] = acc.val then el
    else erec (el @ acc.val)
  in erec el
;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

end ;


module S7LiftLists = struct
  (** in each entry, replace all LIST symbols with a new entry;

   LIST0 sym ->

   entry: [ [ PRIORITY 1; x = sym ; y = entry -> [x :: y]
            | -> [] ] ] ;

================================================================

   LIST0 sym SEP sym2 ->

   entry: [ [ PRIORITY 1; y = LIST1 sym SEP sym2 -> y
            | -> [] ] ] ;

================================================================

   LIST1 sym ->

   entry: [ [ x = sym ; y = LIST0 sym -> [x :: y] ] ] ;

================================================================

   LIST1 sym SEP sym2 ->

   entry: [ [ x = sym ; y = LIST0 [ sym2 ; y = sym -> y ] -> [x :: y] ] ] ;

================================================================

   LIST0 sym SEP sym2 OPT_SEP ->

   entry: [ [ PRIORITY 1 ; x = sym -> [x]
            | PRIORITY 1 ; x = sym ; PRIORITY 1 ; sym2 ; y = entry -> [x :: y]
            | -> []
            ] ] ;

================================================================

   LIST1 sym SEP sym2 OPT_SEP ->

   entry: [ [ x = sym -> [x]
            | x = sym ; PRIORITY 1 ; sym2 ; y = LIST0 sym SEP sym2 OPT_SEP -> [x :: y]
            ] ] ;

================================================================

   *)

open FreeLids ;

(** lift_lists

    This will lift out *outermost* LIST symbols, replacing them
    with ASnterm symbols.

    As we recurse down, we build up an env of freevars, and at the point
    we find a LIST symbol, we intersect with free-lids of the symbol, to
    get the formals of the new entry.
 *)

value list0_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_0 s0 None as s ->
  let new_ename = CG.fresh_name cg e.ae_name in
  let new_x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let new_y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let prio_psl = if g then [{ap_loc=loc; ap_patt=None; ap_symb=ASpriority loc 1}] else [] in
  let rule0 = {ar_loc = loc ; ar_action = Some <:expr< [$lid:new_x$ :: $lid:new_y$] >> ;
               ar_psymbols = prio_psl@[{ap_loc=loc;ap_patt= Some <:patt< $lid:new_x$ >>; ap_symb=s0}
                             ;{ap_loc=loc;ap_patt= Some <:patt< $lid:new_y$ >>
                               ;ap_symb=ASnterm loc new_ename actuals None}]} in
  let rule1 = {ar_loc = loc ; ar_action = Some <:expr< [] >> ; ar_psymbols = []} in
  let rules = {au_loc=loc; au_rules=[rule0; rule1]} in
  let level = {al_loc=loc; al_label=None; al_assoc=None; al_rules=rules} in
  {
    ae_name = new_ename
  ; ae_loc = loc
  ; ae_pos = None
  ; ae_formals = formals
  ; ae_preceding_psymbols = []
  ; ae_levels = [level]
  ; ae_source_symbol = Some s
  }
]
;

value list1_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_1 s0 None as s ->
  let new_ename = CG.fresh_name cg e.ae_name in
  let new_x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let new_y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let s' = ASlist loc g LML_0 s0 None in
  let rule0 = {ar_loc = loc ; ar_action = Some <:expr< [$lid:new_x$ :: $lid:new_y$] >> ;
               ar_psymbols = [{ap_loc=loc;ap_patt= Some <:patt< $lid:new_x$ >>; ap_symb=s0}
                             ;{ap_loc=loc;ap_patt= Some <:patt< $lid:new_y$ >>
                               ;ap_symb=s'}]} in
  let rules = {au_loc=loc; au_rules=[rule0]} in
  let level = {al_loc=loc; al_label=None; al_assoc=None; al_rules=rules} in
  {
    ae_name = new_ename
  ; ae_loc = loc
  ; ae_pos = None
  ; ae_formals = formals
  ; ae_preceding_psymbols = []
  ; ae_levels = [level]
  ; ae_source_symbol = Some s
  }
]
;

value list1sep_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_1 sym (Some (sep, False)) as s ->
  let ename = CG.fresh_name cg e.ae_name in
  let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  { ae_loc = loc
  ; ae_name = ename
  ; ae_pos = None
  ; ae_formals = []
  ; ae_levels =
     [{al_loc = loc; al_label = None; al_assoc = None;
       al_rules =
        {au_loc = loc;
         au_rules = [
             { ar_loc = loc
             ; ar_psymbols = [
                 { ap_loc = loc
                 ; ap_patt = Some <:patt< $lid:x$ >>
                 ; ap_symb = sym
                 }
               ; { ap_loc = loc
                 ; ap_patt = Some <:patt< $lid:y$ >>
                 ; ap_symb = ASlist loc g LML_0
                               (ASrules loc { au_loc = loc
                                            ; au_rules = [{ ar_loc = loc
                                                          ; ar_psymbols = [
                                                              { ap_loc = loc
                                                              ; ap_patt = None
                                                              ; ap_symb = sep
                                                              }
                                                            ; { ap_loc = loc
                                                              ; ap_patt = Some <:patt< $lid:y$ >>
                                                              ; ap_symb = sym
                                                            }]
                                                          ; ar_action = Some <:expr< $lid:y$ >>}]})
                               None
               }]
             ; ar_action = Some <:expr< [$lid:x$ :: $lid:y$] >>
             }
     ]}}]
  ; ae_preceding_psymbols = []
  ; ae_source_symbol = Some s
  }
]
;


value list0sep_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_0 sym (Some (sep, False)) as s ->
  let ename = CG.fresh_name cg e.ae_name in
  let y = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let prio_psl = if g then [{ap_loc=loc; ap_patt=None; ap_symb=ASpriority loc 1}] else [] in
  { ae_loc = loc
  ; ae_name = ename
  ; ae_pos = None
  ; ae_formals = []
  ; ae_levels =
      [{ al_loc = loc
       ; al_label = None
       ; al_assoc = None
       ; al_rules =
           { au_loc = loc
           ; au_rules =
               [{ ar_loc = loc
                ; ar_psymbols = prio_psl@[
                    { ap_loc = loc
                    ; ap_patt = Some <:patt< $lid:y$ >>
                    ; ap_symb = ASlist loc g LML_1 sym (Some (sep, False))
                  }]
                ; ar_action = Some <:expr< $lid:y$ >>
                }
               ; { ar_loc = loc
                 ; ar_psymbols = []
                 ; ar_action = Some <:expr< [] >>
               }]
           }
       }
      ]
  ; ae_preceding_psymbols = []
  ; ae_source_symbol = Some s
  }
]
;

(*
   LIST1 sym SEP sym2 OPT_SEP ->

   entry: [ [ x = sym -> [x]
            | x = sym ; PRIORITY 1 ; sym2 ; y = LIST0 sym SEP sym2 OPT_SEP -> [x :: y]
            ] ] ;
 *)
value list1sep_opt_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_1 sym (Some (sep, True)) as s ->
  let ename = CG.fresh_name cg e.ae_name in
  let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let prio_psl = if g then [{ap_loc=loc; ap_patt=None; ap_symb=ASpriority loc 1}] else [] in

  {ae_loc = loc; ae_name = ename; ae_pos = None; ae_formals = [];
   ae_levels =
     [{al_loc = loc; al_label = None; al_assoc = None;
       al_rules =
         {au_loc = loc;
          au_rules =
            [{ar_loc = loc;
              ar_psymbols =
                [{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>
                  ; ap_symb = sym}];
              ar_action = Some <:expr< [$lid:x$] >>};
              {ar_loc = loc;
               ar_psymbols =
                 [{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>
                   ; ap_symb = sym}]@
                   prio_psl@
                 [{ap_loc = loc; ap_patt = None;
                   ap_symb = sep};
                  {ap_loc = loc; ap_patt = Some <:patt< $lid:y$ >>
                   ; ap_symb = ASlist loc g LML_0 sym (Some (sep, True))}];
               ar_action = Some <:expr< [$lid:x$ :: $lid:y$] >>}]}}]
   ; ae_preceding_psymbols = []
   ; ae_source_symbol = Some s
  }
]
;

(*
   entry: [ [ x = sym -> [x]
            | x = sym ; sym2 ; y = entry -> [x :: y]
            | -> []
            ] ] ;
 *)
value list0sep_opt_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_0 sym (Some (sep, True)) as s ->
  let ename = CG.fresh_name cg e.ae_name in
  let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  
  {ae_loc = loc; ae_name = ename; ae_pos = None; ae_formals = [];
   ae_levels =
     [{al_loc = loc; al_label = None; al_assoc = None;
       al_rules =
         {au_loc = loc;
          au_rules =
            [{ar_loc = loc;
              ar_psymbols =
                [{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>;
                                                              ap_symb = sym}];
              ar_action = Some <:expr< [$lid:x$] >>};
              {ar_loc = loc;
               ar_psymbols =
                 [{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>;
                                                               ap_symb = sym};
                  {ap_loc = loc; ap_patt = None;
                   ap_symb = sep};
                  {ap_loc = loc; ap_patt = Some <:patt< $lid:y$ >>;
                                                               ap_symb = ASnterm loc ename [] None}];
               ar_action = Some <:expr< [$lid:x$ :: $lid:y$] >>};
               {ar_loc = loc; ar_psymbols = []; ar_action = Some <:expr< [] >>}]}}]
   ; ae_preceding_psymbols = []
   ; ae_source_symbol = Some s
  }
]
;

value lift_lists1 (cg : CG.t) acc e =
  let open Llk_migrate in
  let dt = make_dt [] in
  let fallback_migrate_a_entry = dt.migrate_a_entry in
  let migrate_a_entry dt e =
    let dt = {(dt) with aux = e.ae_formals} in
    {(e) with ae_levels = List.map (dt.migrate_a_level dt) e.ae_levels} in

  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASlist loc g LML_0 s0 None as s ->
        let formals = dt.aux in
        let freevars = free_lids_of_a_symbol s0 in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = list0_e cg (formals, actuals) e s in
        do {
          acc.val := [new_e :: acc.val] ;
          ASnterm loc new_e.ae_name actuals None
        }

      | ASlist loc g LML_1 s0 None as s ->
        let formals = dt.aux in
        let freevars = free_lids_of_a_symbol s0 in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = list1_e cg (formals, actuals) e s in
        do {
          acc.val := [new_e :: acc.val] ;
          ASnterm loc new_e.ae_name actuals None
        }

      | ASlist loc g LML_1 s0 (Some (s1, False)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = list1sep_e cg (formals, actuals) e s in

        do {
          acc.val := [new_e :: acc.val] ;
          ASnterm loc new_e.ae_name actuals None
        }

      | ASlist loc g LML_0 s0 (Some (s1, False)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = list0sep_e cg (formals, actuals) e s in

        do {
          acc.val := [new_e :: acc.val] ;
          ASnterm loc new_e.ae_name actuals None
        }

      | ASlist loc g LML_1 s0 (Some (s1, True)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = list1sep_opt_e cg (formals, actuals) e s in

        do {
          acc.val := [new_e :: acc.val] ;
          ASnterm loc new_e.ae_name actuals None
        }

      | ASlist loc g LML_0 s0 (Some (s1, True)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = list0sep_opt_e cg (formals, actuals) e s in

        do {
          acc.val := [new_e :: acc.val] ;
          ASnterm loc new_e.ae_name actuals None
        }

      | s -> fallback_migrate_a_symbol dt s
      ] in

  let fallback_migrate_a_psymbols = dt.migrate_a_psymbols in
  let migrate_a_psymbols dt psl = match psl with [
        [] -> []
      | [h :: t] ->
         let dt' = match h.ap_patt with [
               None -> dt
             | Some p -> {(dt) with aux = dt.aux@[p]}
             ] in
         [ dt.migrate_a_psymbol dt h :: dt'.migrate_a_psymbols dt' t]
      ] in
  let dt = {(dt) with
             migrate_a_entry = migrate_a_entry
           ; migrate_a_psymbols = migrate_a_psymbols
           ; migrate_a_symbol = migrate_a_symbol } in
  dt.migrate_a_entry dt e
;

value lift_lists cg e =
  let acc = ref [] in
  let e = lift_lists1 cg acc e in
  (e, acc.val)
;

value rec exec1_entry (cg : CG.t) e =
  let (e, newel) = lift_lists cg e in
  [e :: List.concat_map (exec1_entry cg) newel]
;

value exec0 cg el =
  List.concat_map (exec1_entry cg) el
;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

end ;

module S8LiftLeftAssoc = struct
  (** in each entry, replace all LEFT_ASSOC symbols with a new entry;

e2:
  [ [ x = LEFT_ASSOC e3 e7 WITH f → x ] ]
;

-->

e2: [ [ x = e4 -> x ] ] ;

e4: [ [ x = e3 ; y = e5[x] -> y ] ]

e5[x]: [ [ PRIORITY 1 ; y = e7 ; z = e5[f x y] -> z
         | -> x ] ] ;

   *)

open FreeLids ;

(** generate entry e5 above *)
value left_assoc_e1 cg (formals, actuals) e = fun [
  ASleft_assoc loc g s1 s2 combiner ->
  let ename = CG.fresh_name cg e.ae_name in
  let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let z = Name.print (CG.fresh_name cg (Name.mk "z")) in
  let prio_ps = {ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1} in
  let prio_psl = if g then [prio_ps] else [] in
  
  {ae_loc = loc; ae_name = ename; ae_pos = None;
   ae_formals = formals@[<:patt< $lid:x$ >>];
   ae_levels =
     [{al_loc = loc; al_label = None; al_assoc = None;
       al_rules =
         {au_loc = loc;
          au_rules =
            [{ar_loc = loc;
              ar_psymbols =
                prio_psl@[{ ap_loc = loc
                 ; ap_patt = Some <:patt< $lid:y$ >>
                 ; ap_symb = s2};
                 { ap_loc = loc
                 ; ap_patt = Some <:patt< $lid:z$ >>
                 ; ap_symb = ASnterm loc ename (actuals@[<:expr< $combiner$ $lid:x$ $lid:y$ >>]) None}];
              ar_action = Some <:expr< $lid:z$ >>};
              { ar_loc = loc
              ; ar_psymbols = []
              ; ar_action = Some <:expr< $lid:x$ >>}]}}]
   ; ae_preceding_psymbols = []
   ; ae_source_symbol = None}
]
;

value left_assoc_e2 cg (formals, actuals) ~{new_e1} e = fun [
  ASleft_assoc loc _ s1 s2 combiner ->
  let ename = CG.fresh_name cg e.ae_name in
  let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  {ae_loc = loc; ae_name = ename; ae_pos = None; ae_formals = formals;
      ae_levels =
       [{al_loc = loc; al_label = None; al_assoc = None;
         al_rules =
          {au_loc = loc;
           au_rules =
            [{ar_loc = loc;
              ar_psymbols =
               [{ap_loc = loc
                ; ap_patt = Some <:patt< $lid:x$ >>
                ; ap_symb = s1};
                {ap_loc = loc
                ; ap_patt = Some <:patt< $lid:y$ >>
                ; ap_symb = ASnterm loc new_e1.ae_name (actuals@[<:expr< $lid:x$ >>]) None}];
              ar_action = Some <:expr< $lid:y$ >>}]}}]
      ; ae_preceding_psymbols = []
      ; ae_source_symbol = None}
]
;


value lift_left_assoc1 (cg : CG.t) acc e =
  let open Llk_migrate in
  let dt = make_dt [] in
  let fallback_migrate_a_entry = dt.migrate_a_entry in
  let migrate_a_entry dt e =
    let dt = {(dt) with aux = e.ae_formals} in
    {(e) with ae_levels = List.map (dt.migrate_a_level dt) e.ae_levels} in

  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASleft_assoc loc _ s1 s2 combiner as s ->
        let formals = dt.aux in
        let freevars = free_lids_of_a_symbol s in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e1 = left_assoc_e1 cg (formals, actuals) e s in
        let new_e2 = left_assoc_e2 cg (formals, actuals) ~{new_e1=new_e1} e s in
        do {
          acc.val := [new_e1 ; new_e2 :: acc.val] ;
          ASnterm loc new_e2.ae_name actuals None
        }

      | s -> fallback_migrate_a_symbol dt s
      ] in

  let fallback_migrate_a_psymbols = dt.migrate_a_psymbols in
  let migrate_a_psymbols dt psl = match psl with [
        [] -> []
      | [h :: t] ->
         let dt' = match h.ap_patt with [
               None -> dt
             | Some p -> {(dt) with aux = dt.aux@[p]}
             ] in
         [ dt.migrate_a_psymbol dt h :: dt'.migrate_a_psymbols dt' t]
      ] in
  let dt = {(dt) with
             migrate_a_entry = migrate_a_entry
           ; migrate_a_psymbols = migrate_a_psymbols
           ; migrate_a_symbol = migrate_a_symbol } in
  dt.migrate_a_entry dt e
;

value lift_left_assoc cg e =
  let acc = ref [] in
  let e = lift_left_assoc1 cg acc e in
  (e, acc.val)
;

value rec exec1_entry (cg : CG.t) e =
  let (e, newel) = lift_left_assoc cg e in
  [e :: List.concat_map (exec1_entry cg) newel]
;

value exec0 cg el =
  List.concat_map (exec1_entry cg) el
;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

end ;

module S9ExpandMacros = struct

open FreeLids ;

(** expand_macros

    expand macros
 *)

value expand_macros (cg : CG.t) e =
  let open Llk_migrate in
  let dt = make_dt [] in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASvala loc sym anti_kinds ->
        let sym = dt.migrate_a_symbol dt sym in
        let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
        ASrules loc
          {au_loc = loc;
           au_rules =
             [{ar_loc = loc;
               ar_psymbols =
                 [{ ap_loc = loc
                  ; ap_patt = Some <:patt< $lid:x$ >>
                  ; ap_symb = sym}];
               ar_action = Some <:expr< Ploc.VaVal $lid:x$ >>};
               {ar_loc = loc;
                ar_psymbols =
                  [{ ap_loc = loc
                   ; ap_patt = Some <:patt< $lid:x$ >>
                   ; ap_symb = ASanti loc anti_kinds}];
                ar_action = Some <:expr< $lid:x$ >>}]}

      | ASflag loc g sym ->
         let sym = dt.migrate_a_symbol dt sym in
         let ps_eps = {ap_loc=loc; ap_patt=None; ap_symb = ASregexp loc check_eps} in
         let rule1_psl = if g then [ps_eps] else [] in
         ASrules loc
           {au_loc = loc;
            au_rules =
              [{ ar_loc = loc
               ; ar_psymbols =
                   [{ ap_loc = loc; ap_patt = None
                      ; ap_symb = sym
                   }]
               ; ar_action = Some <:expr< True >>}
               ;{ ar_loc = loc
                ; ar_psymbols = rule1_psl
                ; ar_action = Some <:expr< False >>}]}

      | ASopt loc g sym ->
         let sym = dt.migrate_a_symbol dt sym in
         let ps_eps = {ap_loc=loc; ap_patt=None; ap_symb = ASregexp loc check_eps} in
         let rule1_psl = if g then [ps_eps] else [] in
         let x = Name.print (CG.fresh_name cg (Name.mk "x")) in

         ASrules loc
                 {au_loc = loc;
                  au_rules =
                   [{ar_loc = loc;
                     ar_psymbols =
                      [{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>;
                        ap_symb = sym}];
                     ar_action = Some <:expr< Some $lid:x$ >>};
                    {ar_loc = loc; ar_psymbols = rule1_psl;
                     ar_action = Some <:expr< None >>}]}

      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = {(dt) with
             migrate_a_symbol = migrate_a_symbol
           } in
  dt.migrate_a_entry dt e
;

value exec0 cg el = List.map (expand_macros cg) el ;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

end ;

module S9SeparateSyntactic = struct
  (** in each entry, separate entries with some rules that start
      with syntactic predicates and some that do not, into two entries,
      one with syntactic predicates, and the other without.
   *)

open FreeLids ;

value is_syntactic_predicate_rule = fun [
  {ar_psymbols=[{ap_symb=ASsyntactic _ _} :: _]} -> True
 | _ -> False
]
;

value sep1_entry cg e = do {
  let loc = e.ae_loc in
  let lev = List.hd e.ae_levels  in
  let rs = lev.al_rules in
  let (sp_rl, nonsp_rl) = Ppxutil.filter_split is_syntactic_predicate_rule rs.au_rules in
  assert ([] <> sp_rl) ;
  let fresh_x = CG.fresh_name cg (Name.mk "__x__") in
  let actuals = formals2actuals cg e.ae_formals in

  let e1_name = CG.fresh_name cg e.ae_name in
  let e0 = {(e) with ae_levels = [{(lev) with al_rules = {(rs) with au_rules = sp_rl @ [
                 { ar_loc=loc
                 ; ar_psymbols=[{ ap_loc=loc
                                ; ap_patt = Some <:patt< $lid:Name.print fresh_x$ >>
                                ; ap_symb = ASnterm loc e1_name actuals None}]
                 ; ar_action = Some <:expr< $lid:Name.print fresh_x$ >> }
               ]}}]} in

  let e1 = { (e) with
             ae_name = e1_name
           ; ae_levels = [{(lev) with al_rules = {(rs) with au_rules = nonsp_rl}}]
           } in
  [e0; e1]
}
;

value sep_entry cg e = do {
  assert (1 = List.length e.ae_levels) ;
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  if not (List.exists is_syntactic_predicate_rule rl) then
    [e]
  else
    sep1_entry cg e
}
;
  
value exec0 cg el =
    List.concat_map (sep_entry cg) el
;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

end ;

module SortEntries = struct

value exec0 el =
  let cmp e1 e2 = Name.compare e1.ae_name e2.ae_name in
  List.stable_sort cmp el ;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 (CG.gram_entries cg) } ;

end ;

(** An empty entry is one of the form:

  e[args]: [ [ x = f[args] -> x ] ] ;

  Such an entry can be eliminated, and all instances of entry "e"
  can be replaced with "f".
 *)

module S4EmptyEntryElim = struct

value empty_rule cg (ename, formals) = fun [
      {ar_psymbols=[{ap_patt= Some <:patt< $lid:patt_x$ >>; ap_symb=ASnterm _ rhsname actuals None}];
       ar_action = Some <:expr< $lid:expr_x$ >> } ->
      if List.length formals = List.length actuals &&
           List.for_all2 equal_expr (formals2actuals cg formals) actuals then
        Some (ename, rhsname)
      else None
    | _ -> None
    ]
;

value empty_level cg (ename, formal) l =
  if 1 = List.length l.al_rules.au_rules then
    empty_rule cg (ename, formal) (List.hd l.al_rules.au_rules)
  else None
;

value gen_re = Pcre.regexp "^([a-zA-Z0-9_]+)__([0-9]{4})(__[0-9]{2})?$" ;
value is_generated_entry_name (_, n) = n > -1 ;

value find_empty_entry cg el =
  el |> List.find_map (fun e ->
      let ename = e.ae_name in
      let formals = e.ae_formals in
      if is_generated_entry_name e.ae_name && 1 = List.length e.ae_levels then
        empty_level cg (ename, formals) (List.hd e.ae_levels)
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

value rec exec0 cg el =
    match find_empty_entry cg el with [
        None -> el
      | Some (ename, rhsname) ->
         let rest_el = List.filter (fun e' -> ename <> e'.ae_name) el in
         exec0 cg (List.map (eliminate_empty_entry (ename, rhsname)) rest_el)
    ]
;

value exec cg = CG.withg cg {(CG.g cg) with gram_entries = exec0 cg (CG.gram_entries cg) } ;

end ;

(** Infer a regular expression from a rule.

    the invariant we maintain is that each inference routine returns a pair
    of regexp * bool, where the bool is true when the regexp is "complete".

    So an incomplete regexp might still be useful, and to ensure that, we only
    use an incomplete regexp when it is nonempty.

 *)
module Infer = struct
open PatternBaseToken ;

value rec infer_symbol cg stk ename = fun [
   ASflag _ _ s | ASopt _ _ s ->
   (match infer_symbol cg stk ename s with [
        (re, False) ->
            if PSyn.empty re then (PSyn.epsilon, False)
            else (PSyn.(disjunction [re; epsilon]), False)
      | (re, True) -> (PSyn.(disjunction [re; epsilon]), True)
      ])

  | ASkeyw _ kw -> (PSyn.token (SPCL kw), True)
  | ASlist _ _ LML_1 s _ ->
     let (re, _) = infer_symbol cg stk ename s in
     (re, False)

  | ASlist _ _ _ _ _ -> (PSyn.epsilon, False)
  | ASnext _ _ -> assert False
  | ASnterm _ nt _ (Some _) -> assert False
  | ASnterm _ nt _ None when not (CG.exists_entry cg nt) -> assert False
  | ASnterm _ nt _ None ->
     let e = CG.gram_entry cg nt in
     infer_entry cg stk e

  | ASregexp loc rexname ->
     (match CG.gram_regexp cg rexname with [
          exception Not_found -> do {
            CG.add_failuref cg (CG.adjust_loc cg loc) ename "infer_symbol: undefined regexp %s" (Name.print rexname) ;
            failwith "caught"
          }
        | x -> (x, True)
     ])

  | ASsyntactic _ _ -> (PSyn.epsilon, False)

  | ASleft_assoc _ _ s _ _ ->
     let (re, _) = infer_symbol cg stk ename s in
     (re, False)

  | ASrules _ _ -> assert False
  | ASself _ _ -> assert False
  | AStok _ cls None -> (PSyn.token (CLS cls None), True)
  | AStok _ cls (Some tok) -> (PSyn.token (CLS cls (Some tok)), True)

  | ASvala _ s sl ->
     let anti_re =
       sl
       |> List.concat_map (fun s -> PSyn.[token (ANTI s); token (ANTI ("_"^s))])
       |> PSyn.disjunction in
     (match infer_symbol cg stk ename s with [
          (re, False) ->
          if PSyn.empty re then (PSyn.epsilon, False)
          else (PSyn.(disjunction [re; anti_re]), False)
        | (re, True) -> (PSyn.(disjunction [re; anti_re]), True)
     ])

  | ASanti _ sl ->
     let anti_re =
       sl
       |> List.concat_map (fun s -> PSyn.[token (ANTI s); token (ANTI ("_"^s))])
       |> PSyn.disjunction in
     (anti_re, True)

  | ASpriority _ _ -> assert False
]

and infer_entry cg stk e =
  if List.mem e.ae_name stk then (PSyn.epsilon, False) else
  let stk = [ e.ae_name :: stk ] in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  let rex_comp_l = List.map (infer_rule cg stk e.ae_name) rl in
  if List.for_all snd rex_comp_l then
    (rex_comp_l |> List.map fst |> PSyn.disjunction, True)
  else if List.for_all (fun (re, _) -> not (PSyn.empty re)) rex_comp_l then
    (rex_comp_l |> List.map fst |> PSyn.disjunction, False)
  else (PSyn.epsilon, False)

and infer_rule cg stk ename r = infer_psymbols cg stk ename r.ar_psymbols

and infer_psymbols cg stk ename = fun [
      [ {ap_symb = (ASregexp _ _ as s)} :: _ ] ->
      infer_symbol cg stk ename s

    | [ {ap_symb = (ASinfer _ _)} :: t ] -> infer_psymbols cg stk ename t
    | [ {ap_symb = (ASpriority _ _)} :: t ] -> infer_psymbols cg stk ename t

    | [ h :: t ] ->
       (match infer_psymbol cg stk ename h with [
            (h_re, False) -> (h_re, False)
          | (h_re, True) ->
             (match infer_psymbols cg stk ename t with [
                  (t_re, False) -> (PSyn.(h_re @@ t_re), False)
                | (t_re, True) -> (PSyn.(h_re @@ t_re), True)
             ])
       ])
    | [] -> (PSyn.epsilon, True)
]

and infer_psymbol cg stk ename ps = infer_symbol cg stk ename ps.ap_symb
;

value regexp_of_rule cg ename r =
  match infer_rule cg [] ename r with [
      (rex, False) when PSyn.empty rex -> do {
        CG.add_failure cg (CG.adjust_loc cg r.ar_loc) ename "Infer.top_infer_rule: empty regexp" ;
        failwith "caught"
      }

    | (rex, False) -> rex
    | (rex, True) -> rex
    ]
;

value length_regexp_of_rule cg ename r length =
  let open Brzozowski2.GenericRegexp in
  let fullre = regexp_of_rule cg ename r in
  let rec lenrec length rex =
    if length = 0 then (PSyn.epsilon, 0)
    else
      match skeleton rex with [
          EEpsilon -> (PSyn.epsilon, length)
        | EToken tok -> (PSyn.token tok, length - 1)
        | ECat re1 re2 ->
           let (re1', length) = lenrec length re1 in
           let (re2', length) = lenrec length re2 in
           (PSyn.(re1' @@ re2'), length)

        | EDisj [] -> assert False
        | EDisj l ->
           let re_length_l = List.map (lenrec length) l in
           let length = List.fold_left (fun length (_, length') -> max length length')
                      (snd (List.hd re_length_l)) (List.tl re_length_l) in
           (PSyn.disjunction (List.map fst re_length_l), length)

        | EStar _ -> assert False
        | EConj _ -> assert False
        | ENeg _ -> assert False
        ] in
  fst (lenrec length fullre)
;

end ;

(** Build the ATN NFA for this grammar
*)
module ATN = struct

include ATN0 ;

module Build = struct
value symbol it (snode, enode) = fun [
  ASflag _ _ _ | ASopt _ _ _
  | ASlist _ _ _ _ _
  | ASnext _ _
  | ASnterm _ _ _ (Some _)
  | ASrules _ _
  | ASself _ _
  | ASvala _ _ _
  | ASleft_assoc _ _ _ _ _

  -> assert False

  | ASkeyw _ tok -> Raw.add_edge it (snode, Some (SPCL tok), enode)
  | ASnterm _ nt _ None -> do {
    let (snode', enode') = Raw.entry_nodes it nt in
    Raw.add_edge it (snode, None, snode') ;
    Raw.add_edge it (enode', None, enode)
  }

  | ASregexp _ _
  | ASinfer _ _
  | ASpriority _ _
  | ASsyntactic _ _

    -> Raw.add_edge it (snode, None, enode)

  | AStok _ cls tokopt ->
    Raw.add_edge it (snode, Some (CLS cls tokopt), enode)

  | ASanti _ anti_kinds ->
    let l = anti_kinds |> List.concat_map (fun s -> [(ANTI s); (ANTI ("_"^s))]) in
    l |> List.iter (fun tok ->
        Raw.add_edge it (snode, Some tok, enode))
  ]
;

value rec psymbols it (snode, enode) = fun [
  [] -> Raw.add_edge it (snode, None, enode)
| [h] -> symbol it (snode, enode) h.ap_symb
| [h :: t] -> do {
    let mid = Raw.new_node it in
    symbol it (snode, mid) h.ap_symb ;
    psymbols it (mid, enode) t
  }
]
;

value rule it (snode, enode) r =
  psymbols it (snode, enode) r.ar_psymbols ;

value entry it e =
  let (e_snode, e_enode) = Raw.entry_nodes it e.ae_name in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  rl
  |> List.iteri (fun i r ->
         let r_snode = Raw.start_entry_branch it e.ae_name i in
         rule it (r_snode, e_enode) r
       )
;

value external_entry cg it (ename, rex) =
  let (snode, enode) = Raw.entry_nodes it ename in
  let module C = Compile(struct value rex = rex ; value extra = (CG.alphabet cg); end) in
  let is_nullable = C.BEval.nullable rex in
  let nulls = if is_nullable then [None] else [] in
  let toks = List.map (fun x -> Some x) (C.BEval.OutputDfa.first_tokens rex) in
  (toks@nulls)
  |> List.iter (fun [
    Some tok ->
    let n' = Raw.new_node it in do {
      Raw.add_edge it (snode, Some tok, n') ;
      Raw.mark_bhole it n'
    }
  | None -> Raw.mark_bhole it snode
  ])
;

value grammar it cg = do {
  (CG.gram_entries cg) |> List.iter (entry it) ;
  (CG.g cg).gram_exports
  |> List.iter (fun ename -> 
         let (snode, enode) = Raw.entry_nodes it ename in do {
                  Raw.mark_initial it snode ;
                  Raw.mark_final it enode ;
                  Raw.add_edge it (enode, Some (CLS "EOI" None), enode)
                }
       ) ;
  (CG.gram_externals cg) |> List.iter (external_entry cg it)
}
;
end ;

value eclosure it n =
  let acc = ref [n] in
  let rec erec n =
    Raw.traverse it n None
    |> List.iter (fun n' ->
           if (not (List.mem n' acc.val)) then do {
             Std.push acc n' ;
             erec n'
           }
           else ()
         )
  in do {
    erec n ;
    acc.val
  }
;

value epsilon_closure it : MHM.t Node.t (list Node.t) = do {
  let ht = MHM.mk 23 in
  (Raw.nodes it)
  |> List.iter (fun n ->
         let l = eclosure it n in
         MHM.add ht (n, l)
       ) ;
  ht
}
;

(** step1 [it,ec] [st]:

    From state [st], take one non-epsilon step in the ATN
    returning the list of (tok * st) that are reached.
 *)

value step1 loc (it, ec) (st : Node.t) = do {
  if Raw.is_bhole it st then
    raise_failwithf loc "ATN.step1: cannot explore tokens forward from bhole node: %s" (Node.print st)
  else () ;
  let acc = ref [] in
  MHM.map ec st
  |> List.iter (fun st ->
         let labs = Raw.edge_labels it st in
         labs
         |> List.iter (fun [
            None -> ()
          | (Some tok) as lab ->
             let dsts = Raw.traverse it st lab in
             dsts |> List.iter (fun dst -> Std.push acc (tok, dst))
              ])
       ) ;
  List.sort_uniq Stdlib.compare acc.val
}
;

value node_first loc ((atn : Raw.t),ec) node =
  let l = step1 loc (atn, ec) node in
  List.map fst l |> List.sort_uniq PatternBaseToken.compare
;

value entry_first cg e =
  let ((atn : Raw.t),ec) = CG.gram_atn_ec cg in
  let (snode, _) = Raw.entry_nodes atn e.ae_name in
  node_first e.ae_loc (atn, ec) snode
;

value branch_first (cg : CG.t) e =
  let ((atn : Raw.t),ec) = CG.gram_atn_ec cg in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  rl
  |> List.mapi (fun i _ ->
         let node = Raw.entry_branch atn e.ae_name i in
         (i, node_first e.ae_loc (atn, ec) node))
;

module TokPath = struct
type t = { branchnum : int ; priority : option int ; tokpath : list token ; states : list Node.t } ;
value branchnum p = p.branchnum ;
value priority p = p.priority ;
value tokpath p = p.tokpath ;
value states p = p.states ;
end ;
module TP = TokPath ;


(** extend1 ([branchnum], [toks], [states])

    for each st in states:
      for each token t in one step from st
        let stl' be the states reachable from st by token t:
          return (branchnum, toks@[t], stl')

 *)
value extend1 loc cg t =
  t.states
|> List.concat_map (fun st ->
       step1 loc (CG.gram_atn_ec cg) st
       |> List.map (fun (tok, st') -> {TP.branchnum=t.TP.branchnum; priority=t.priority; tokpath = t.tokpath@[tok]; states= [st']})
     )
;

(** a partition-set is ambiguous if:

    (1) a partition has empty token-list
    (2) any partition has length>1 and priorities are not distinct
 *)

value ambiguous (ll : list (list TP.t)) =
  ll |> List.exists (fun [
    [{TP.tokpath=[]} :: _] -> True
  | l -> not (Std.distinct (List.map TP.priority l))
  ])
;

(** extend_branches:

  (1) partition by token-list
  (2) the current set is ambiguous if any partition has length>1 or token-list=[]
  (3) if not ambiguous
  (4) for each length>1 partition, use [extend1] to extend each element
  (5) partition by (branch-num, token-list) and union the state-sets
 *)
type branches_toks_list = list TP.t ;
value extend_branches loc (cg : CG.t) (l : branches_toks_list) : (bool * branches_toks_list) =
  let open TP in
  let ll = Std.nway_partition (fun p1 p2 -> p1.tokpath = p2.tokpath) l in
  if not (ambiguous ll) then (True, l) else
  let l = ll |> List.concat_map (fun [
    [{tokpath=[_ :: _]}] as l -> l
  | l -> l |> List.concat_map (extend1 loc cg)
  ]) in
  let ll = Std.nway_partition (fun p1 p2 -> p1.branchnum=p2.branchnum && p1.tokpath=p2.tokpath) l in
  let l = ll |> List.map (fun l ->
    let p0 = List.hd l in
    {(p0) with states = List.concat_map TP.states l}) in
  (False, l)
;

end ;

module BuildATN = struct

value exec cg = do {
  ATN.Build.grammar (CG.gram_atn cg) cg ;
  let eclosure = ATN.epsilon_closure(CG.gram_atn cg) in
  (snd cg).eclosure := eclosure ;
  cg
}
;
end ;

module ATNFirst = struct

value store_entry_branch_first cg e =
  let l = ATN.branch_first cg e in
  CG.set_atn_first cg e.ae_name l
;

value rec compute_firstk_depth loc cg ename ~{depth} l =
  if depth = 0 then
    raise_failwithf (CG.adjust_loc cg loc) "compute_firstk_depth(%s): exceeded depth and still ambiguous" (Name.print ename)
  else
    let (complete, l') = ATN.extend_branches loc cg l in
    if complete then l
    else compute_firstk_depth loc cg ename ~{depth=depth-1} l'
;

value compute_firstk ~{depth} cg e =
  let open ATN in
  let open TP in
  let (atn,ec) = CG.gram_atn_ec cg in
  let l =
    (List.hd e.ae_levels).al_rules.au_rules
    |> List.mapi (fun i r ->
           let node = ATN.Raw.entry_branch atn e.ae_name i in
           let priority = match r.ar_psymbols with [
             [{ap_symb=ASpriority _ n} :: _] -> Some n
           | _ -> None
           ] in
           {branchnum=i; priority=priority; tokpath=[]; states=[node]}) in
  let l = compute_firstk_depth e.ae_loc cg e.ae_name ~{depth=depth} l in
  let l =
    l
    |> Std.nway_partition (fun p1 p2 -> TP.tokpath p1 = TP.tokpath p2)
    |> List.map (fun [
         [] -> assert False
       | [x] -> x
       | l -> do {
           assert (Std.distinct (List.map TP.priority l)) ;
           List.fold_left (fun p1 p2 ->
               match (p1.priority, p2.priority) with [
                   (None, Some _) -> p2
                 | (Some _, None) -> p1
                 | (Some n, Some m) when n < m -> p1
                 | (Some n, Some m) when n > m -> p1
                 | _ -> assert False
                 ]
             ) (List.hd l) (List.tl l)
         }
       ]) in
  l
  |> Std.nway_partition (fun p1 p2 -> p1.branchnum=p2.branchnum)
  |> List.map (fun l ->
         let p0 = List.hd l in
         (p0.branchnum, List.map TP.tokpath l))
;

value store_firstk cg e =
  let lopt = match compute_firstk ~{depth=4} cg e with [
        x -> Some x
      | exception exn ->
         let msg = Printexc.to_string exn in do {
          Fmt.(pf stderr "%s\n%!" msg) ;
          None
        }
      ] in
  CG.set_atn_firstk cg e.ae_name lopt
;

value exec cg = do {
    (CG.gram_entries cg)
    |> List.iter (store_firstk cg) ;
    (CG.gram_entries cg)
    |> List.iter (store_entry_branch_first cg) ;
    cg
}
;

end ;

module CheckATNFirst = struct

value compute_fifo cg loc ff r =
  let fi = First.rule cg r in
  (fi, ff, r)
;

value entry_branches_fifo cg e =
  let loc = e.ae_loc in
  let ff = CG.follow cg e.ae_name in
  let fi_fo_rule_list =
    match (List.hd e.ae_levels).al_rules.au_rules
          |> List.map (compute_fifo cg loc ff) with [
      x -> x
    | exception First.ExternalEntry eename -> do {
        CG.add_warning cg (CG.adjust_loc cg loc) eename "compile1a_entry: entry is external, FIRST/FOLLOW disallowed" ;
        failwith "caught"
      }
    ] in
  fi_fo_rule_list
  |> List.mapi (fun i (fi, fo, r) ->
         let raw_tokens =
           TS.export (Follow.fifo_concat cg loc ~{if_nullable=True} fi fo) in
         (i, raw_tokens)
       )
;


value exec cg = do {
  (CG.gram_entries cg)
  |> List.iter (fun e ->
      let loc = e.ae_loc in
      let atn_branch_fifo = CG.atn_first cg e.ae_name in
      let fifo_branch_fifo = entry_branches_fifo cg e in
      if atn_branch_fifo <> fifo_branch_fifo then
        raise_failwithf  (CG.adjust_loc cg loc) "CheckATNFirst: fifo sets differ"
      else ()
    ) ;
  cg
}
; 

end ;

(** Codegen:

  0. compute the set of all tokens/classes.
  1. Each entry A has at most a disjunction of rules.
  2. for each production "A -> w":

  3. compute [FIRST w].{if_nullable}.[FOLLOW A] for each production

  4. each branch of the parsing function gets its patterns from the intersection of #0 and #3.
 *)

module Codegen = struct
open Llk_regexps ;
open PatternBaseToken ;


value all_tokens el =
  let open Llk_migrate in
  let acc = ref [] in
  let dt = make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt s = do { match s with [
          ASkeyw _ s0 -> Std.push acc (SPCL s0)
        | AStok _ s0 tokopt -> Std.push acc (CLS s0 tokopt)
        | ASvala _ s0 sl -> do {
            ignore (dt.migrate_a_symbol dt s0) ;
            List.iter (fun s2 -> Std.push acc (ANTI s2)) sl
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

value compute_fifo cg loc ff r =
  let fi = First.rule cg r in
  (fi, ff, r)
;

value disjoint cg loc ll =
  let rec drec acc = fun [
        [] -> True
      | [(fi, ff,_) :: t] ->
         let h = Follow.fifo_concat cg loc ~{if_nullable=True} fi ff in
         TS.disjoint acc h
         && drec (TS.union h acc) t
      ] in
  drec TS.mt ll
;

value report_verbose = ref False ;

value dump_gram oc cg msg = do {
  Fmt.(pf stderr "================================ %s ================================\n%!" msg) ;
  let pctxt = if report_verbose.val then Pr.normal else Pr.errmsg in
  Fmt.(pf stderr "================================================================\n") ;
  (CG.gram_entries cg)
  |> List.iter (fun e ->  do {
    let fi = CG.first cg e.ae_name in
    let fo = CG.follow cg e.ae_name in
    Fmt.(pf stderr "Entry: %s\nFirst: %s\nFollow: %s\n"
           Pr.(entry ~{pctxt=pctxt} Pprintf.empty_pc e)
           (TS.print print_token_option fi) (TS.print PatternBaseToken.print fo)
        ) ;
    (match CG.atn_first cg e.ae_name with [
       atnfi ->
       let pp_branch pps (n, l) = Fmt.(pf pps "[%a] -> %d" (list ~{sep=const string ", "} PatternBaseToken.pp) l n) in
       Fmt.(pf stderr "ATN First:\n\t%a\n" (list ~{sep=const string "\n\t"} pp_branch) atnfi)
     | exception Not_found -> ()
     ]) ;
    (match CG.atn_firstk cg e.ae_name with [
       Some atnfi ->
       let pp_branch pps (n, ll) =
         let pp1 pps l = Fmt.(pf pps "[%a] -> %d" (list ~{sep=const string " "} PatternBaseToken.pp) l n) in
         Fmt.(pf pps "%a" (list ~{sep=const string "\n\t"} pp1) ll) in
       Fmt.(pf stderr "ATN First(k):\n\t%a\n" (list ~{sep=const string "\n\t"} pp_branch) atnfi)

     | None -> Fmt.(pf stderr "ATN First(k): failed to compute\n")

     | exception Not_found -> ()
     ]) ;
     Fmt.(pf stderr "\n====\n%!")
  }) ;
  Fmt.(pf stderr "================================================================\n") ;
  prerr_string Pr.(top ~{pctxt=pctxt} Pprintf.empty_pc (CG.g cg)) ;
  Fmt.(pf stderr "\n%!")
}
;

value report_compilation_errors cg msg = do {
  dump_gram stderr cg msg ;
  Fmt.(pf stderr "================================================================\n") ;
  (cg |> CG.errors |> List.rev)
  |> List.iter CG.(fun err ->
         Fmt.(pf stderr "%s%s: entry %s: %s\n%s\n"
                (Ploc.string_of_location err.loc)
                err.kind
                (Name.print err.ename)
                err.msg
                (if report_verbose.val then err.backtrace else "")
         )
       ) ;
  Fmt.(pf stderr "\n%!")
}
;

open Exparser ;

value expected_psymbols_msg e left_psymbols ps_opt_l = do {
  assert ([] <> ps_opt_l) ;
  let left_txt = Pr.(rule_psymbols ~{pctxt=errmsg} Pprintf.empty_pc left_psymbols) in
  let pr_ps_opt = fun [
        None -> "<empty>"
      | Some ps -> Pr.(psymbol ~{pctxt=errmsg} Pprintf.empty_pc ps)
      ] in
  let psl_txt = String.concat "] or [" (List.map pr_ps_opt ps_opt_l) in
  Fmt.(str "[%s] expected after [%s] (in [%s])"
         (String.escaped psl_txt)
         (String.escaped left_txt)
         (Name.root e.ae_name)
  )
}
;

value illegal_begin_msg e fifotxt =
  Fmt.(str "illegal begin of %s (legal tokens: %s)" (Name.print e.ae_name) (String.escaped fifotxt))
;

value rec compile1_symbol cg loc e s =
  match s with [
      ASflag loc g s -> do {
        let s_body = compile1_symbol cg loc e s in
        (* <:expr< parser [ [: _ = $s_body$ :] -> True | [: :] -> False ] >> *)
        <:expr< parse_flag $s_body$ >>
      }

    | ASopt loc g s -> do {
        let s_body = compile1_symbol cg loc e s in
        <:expr< parse_opt $s_body$ >>
       }

    | ASkeyw  loc kws ->
       (* <:expr< parser [ [: `("", $str:kws$) :] -> () ] >> *)
       Exparser.(cparser loc (None,
        [([((SpTrm loc <:patt< ("", $str:kws$) >> <:vala<  None >>), SpoNoth)],
          None, <:expr< () >>)]))

    | ASnterm loc nt actuals None when CG.exists_entry cg nt ->
       Expr.applist <:expr< $lid:Name.print nt$ >> actuals

    | ASnterm loc nt actuals None when CG.exists_external_ast cg nt ->
       <:expr< Grammar.Entry.parse_token_stream $lid:Name.print nt$ >>

    | AStok loc cls None ->
       (* <:expr< parser [ [: `($str:cls$, __x__) :] -> __x__ ] >> *)
       Exparser.(cparser loc (None,
        [([((SpTrm loc <:patt< ($str:cls$, __x__) >> <:vala<  None >>), SpoNoth)],
          None, <:expr< __x__ >>)]))

    | AStok loc cls (Some tok) ->
       (* <:expr< parser [ [: `($str:cls$, __x__) :] -> __x__ ] >> *)
       Exparser.(cparser loc (None,
        [([((SpTrm loc <:patt< ($str:cls$, ($str:String.escaped tok$ as __x__)) >> <:vala<  None >>), SpoNoth)],
          None, <:expr< __x__ >>)]))

    | ASlist loc _ LML_0 elem None ->
       let elem = compile1_symbol cg loc e elem in
       <:expr< parse_list0 $elem$ >>

    | ASlist loc _ LML_1 elem None ->
       let elem = compile1_symbol cg loc e elem in
       <:expr< parse_list1 $elem$ >>

    | ASlist loc _ LML_0 elem (Some (sep, False)) ->
       let elem = compile1_symbol cg loc e elem in
       let sep = compile1_symbol cg loc e sep in
       <:expr< parse_list0_with_sep $elem$ $sep$ >>

    | ASlist loc _ LML_1 elem (Some (sep, False)) ->
       let elem = compile1_symbol cg loc e elem in
       let sep = compile1_symbol cg loc e sep in
       <:expr< parse_list1_with_sep $elem$ $sep$ >>

    | ASlist loc _ LML_0 elem (Some (sep, True)) ->
       let elem = compile1_symbol cg loc e elem in
       let sep = compile1_symbol cg loc e sep in
       <:expr< parse_list0_with_sep_opt_trailing $elem$ $sep$ >>

    | ASlist loc _ LML_1 elem (Some (sep, True)) ->
       let elem = compile1_symbol cg loc e elem in
       let sep = compile1_symbol cg loc e sep in
       <:expr< parse_list1_with_sep_opt_trailing $elem$ $sep$ >>


(*
    | ASleft_assoc loc lhs restrhs e ->
 *)       

    | s -> do {
        CG.add_failuref cg (CG.adjust_loc cg loc) e.ae_name "compile1_symbol: %s" Pr.(symbol~{pctxt=errmsg} Pprintf.empty_pc s) ;
        failwith "caught"
      }
    ]

and compile1_psymbol cg loc e must_parse left_psymbols ps =
  let must exp =
    if must_parse then
      let msg = expected_psymbols_msg e left_psymbols [Some ps] in
      <:expr< Pa_llk_runtime.Llk_runtime.must_parse ~{msg= $str:String.escaped msg$ } $exp$ >>
    else exp
  in
  let patt = match ps.ap_patt with [ None -> <:patt< _ >> | Some p -> p ] in
  match ps.ap_symb with [
      ASflag loc _ s -> do {
        let s_body = compile1_symbol cg loc e s in
        (SpNtr loc patt (must <:expr< parse_flag $s_body$ >>), SpoNoth)
       }
    | ASopt loc _ s -> do {
        let s_body = compile1_symbol cg loc e s in
        (SpNtr loc patt (must <:expr< parse_opt $s_body$ >>), SpoNoth)
       }
    | ASkeyw  loc kws when ps.ap_patt = None ->
       (* <:expr< parser [ [: `("", $str:kws$) :] -> () ] >> *)
       ((SpTrm loc <:patt< ("", $str:kws$) >> <:vala<  None >>), SpoNoth)
    | ASkeyw  loc kws when ps.ap_patt <> None ->
       (* <:expr< parser [ [: `("", $str:kws$) :] -> () ] >> *)
       ((SpTrm loc <:patt< ("", ($str:kws$ as $patt$)) >> <:vala<  None >>), SpoNoth)

    | ASnterm loc nt actuals None when CG.exists_entry cg nt ->
       let exp = Expr.applist <:expr< $lid:Name.print nt$ >> actuals in
        (SpNtr loc patt (must exp), SpoNoth)

    | ASnterm loc nt [] None when CG.exists_external_ast cg nt ->
       let exp = <:expr< Grammar.Entry.parse_token_stream $lid:Name.print nt$ >> in
        (SpNtr loc patt (must exp), SpoNoth)

    | AStok loc cls None ->
       (* <:expr< parser [ [: `($str:cls$, __x__) :] -> __x__ ] >> *)
       ((SpTrm loc <:patt< ($str:cls$, $patt$) >> <:vala<  None >>), SpoNoth)

    | AStok loc cls (Some tok) ->
       (* <:expr< parser [ [: `($str:cls$, __x__) :] -> __x__ ] >> *)
       let patt = match patt with [
             <:patt< _ >> -> <:patt< $str:String.escaped tok$ >>
           | _ -> <:patt< ($str:String.escaped tok$ as $patt$) >> ] in
       ((SpTrm loc <:patt< ($str:cls$, $patt$) >> <:vala<  None >>), SpoNoth)

    | ASleft_assoc loc _ lhs restrhs exp ->
       let lhs = compile1_symbol cg loc e lhs in
       let restrhs = compile1_symbol cg loc e restrhs in
       let exp = <:expr< parse_left_assoc $lhs$ $restrhs$ $exp$ >> in
        (SpNtr loc patt (must exp), SpoNoth)

    | ASlist _ _ _ _ _ as s ->
       let exp = compile1_symbol cg loc e s in
       (SpNtr loc patt (must exp), SpoNoth)

    | ASvala loc elem anti_kinds ->
       let kinds_list_expr =
         anti_kinds
         |> List.concat_map (fun k -> [k; "_"^k])
         |> List.map (fun k -> <:expr< $str:k$ >>)
         |> Ppxutil.convert_up_list_expr loc in
       let elem = compile1_symbol cg loc e elem in
       let exp = <:expr< parse_antiquot $elem$ $kinds_list_expr$ >> in
       (SpNtr loc patt (must exp), SpoNoth)

    | ASanti loc anti_kinds ->
       let kinds_list_expr =
         anti_kinds
         |> List.concat_map (fun k -> [k; "_"^k])
         |> List.map (fun k -> <:expr< $str:k$ >>)
         |> Ppxutil.convert_up_list_expr loc in
       let exp = <:expr< parse_antiquot_token $kinds_list_expr$ >> in
       (SpNtr loc patt (must exp), SpoNoth)

    | s -> do {
        CG.add_failuref cg (CG.adjust_loc cg (loc_of_a_symbol s)) e.ae_name "compile1_psymbol: %s" Pr.(symbol~{pctxt=errmsg} Pprintf.empty_pc s) ;
        failwith "caught"
      }
    ]
;

value compile1_psymbols cg loc e psl =
  let rec crec must lefts = fun [
        [({ap_symb=ASregexp _ _} as ps) :: t] -> crec must (lefts@[ps]) t
      | [({ap_symb=ASinfer _ _} as ps) :: t] -> crec must (lefts@[ps]) t
      | [({ap_symb=ASpriority _ _} as ps) :: t] -> crec must (lefts@[ps]) t
      | [] -> []
      | [h ::t] -> [compile1_psymbol cg loc e must lefts h :: crec True (lefts@[h]) t]
      ] in crec False e.ae_preceding_psymbols psl
;

value compile1_rule cg e r =
  let loc = r.ar_loc in
  let r = match r with [
        {ar_action = None ; ar_psymbols=[{ap_patt=None; ap_symb=ASkeyw _ kw}]} ->
        { (r) with ar_action = Some <:expr< $str:kw$ >> }
      | r -> r ] in
  let spc_list = compile1_psymbols cg loc e r.ar_psymbols in
  let action = match r.ar_action with [ None -> <:expr< () >> | Some a -> a ] in
  let freelids = FreeLids.free_lids_of_expr action in
  if List.mem "loc" freelids then
    let action = <:expr< let loc = Grammar.loc_of_token_interval bp ep in $action$ >> in
    cparser loc (Some <:patt< bp >>, [(spc_list, Some <:patt< ep >>, action)])
  else
    cparser loc (None, [(spc_list, None, action)])
;

value tokens_to_match_branches loc i toks =
  let (antis, rest) = Ppxutil.filter_split (fun [ ANTI _ -> True | _ -> False ]) toks in
  let (specifics, rest) = Ppxutil.filter_split (fun [ CLS _ (Some _) -> True | _ -> False ]) rest in
  let rest_branches =
    rest
    |> List.map (fun [
         CLS s None -> (<:patt< Some ($str:s$, _) >>, <:vala< None >>, <:expr< $int:string_of_int i$ >>)
       | CLS s (Some tok) -> assert False
       | SPCL s -> (<:patt< Some ("", $str:s$) >>, <:vala< None >>, <:expr< $int:string_of_int i$ >>)
         ]) in
  let specific_branches =
    specifics
    |> List.map (fun [
         CLS s (Some tok) -> (<:patt< Some ($str:s$, $str:String.escaped tok$) >>, <:vala< None >>, <:expr< $int:string_of_int i$ >>)
       | _ -> assert False
         ]) in
  let anti_branches =
    if antis = [] then [] else
    let kinds = antis |> List.map (fun [ ANTI s -> s ]) in
    let kinds_list_expr = 
      kinds
      |> List.map (fun s -> <:expr< $str:s$ >>)
      |> Ppxutil.convert_up_list_expr loc in
     let whene = <:expr< match Plexer.parse_antiquot x with [
                             Some (k, _) -> List.mem k $kinds_list_expr$
                           | _ -> False
                           ] >> in
     [(<:patt< Some ("ANTIQUOT", x) >>, <:vala< Some whene >>, <:expr< $int:string_of_int i$ >>)]
  in specific_branches @ rest_branches @ anti_branches
;

value match_nest_branches (cg : CG.t) (e : a_entry) i (fi, fo, r) =
  let loc = r.ar_loc in
  let raw_tokens =
    TS.export (Follow.fifo_concat cg loc ~{if_nullable=True} fi fo) in
  let nullable_branch =
    if Follow.nullable fi && TS.mt = fo then
      [(<:patt< _ >>, <:vala< None >>, <:expr< $int:string_of_int i$ >>)]
    else [] in
  ((tokens_to_match_branches loc i raw_tokens) @ nullable_branch, raw_tokens)
;

value build_match_nest loc (cg : CG.t) (e : a_entry) fi_fo_rule_list =
  let branches_fifo_list =
    fi_fo_rule_list
    |> List.mapi (match_nest_branches cg e) in
  let branches = branches_fifo_list |> List.concat_map fst  in
  let fifo = branches_fifo_list |> List.concat_map snd in
  let fifotxt =
    fifo
    |> List.map PSyn.token
    |> PSyn.disjunction
    |> PSyn.print in
  let (null_branches, normal_branches) =
    Ppxutil.filter_split (fun [ (<:patt< _ >>, _, _) -> True | _ -> False ]) branches in
  let null_branches = match null_branches with [
        [] ->
        (match e.ae_preceding_psymbols with [
             [] ->
             [(<:patt< _ >>, <:vala< None >>, <:expr< raise Stream.Failure >>)]
           | left_syms ->
              let psl =
                fi_fo_rule_list
                |> List.map (fun (_, _, r) ->
                       match r.ar_psymbols with [ [] -> None | [h :: _] -> Some h ]) in
              let msg = expected_psymbols_msg e left_syms psl in
              [(<:patt< _ >>, <:vala< None >>, <:expr< raise (Stream.Error $str:msg$) >>)]
           ])
      | [_] as l -> l
      | _ ->  do {
         CG.add_failure cg (CG.adjust_loc cg loc) e.ae_name "internal error in build_match_nest: entry has more than one NULL branch" ;
         failwith "caught"
        }
      ] in
  let branches = normal_branches @ null_branches in
  (<:expr< fun __strm__ -> match Stream.peek __strm__ with [ $list:branches$ ] >>,
   fifotxt)
;

value compile1a_branch cg e i (fi, fo, r) =
  let loc = r.ar_loc in
  let body = compile1_rule cg e r in
  (<:patt< $int:string_of_int i$ >>, <:vala< None >>, body)
;

(** FIRST/FOLLOW compilation strategy.

    1. compute FIRST/FOLLOW for each branch of the rule
    2. combine FIRST.{if_nullable}.FOLLOW -> FFO
    3. if these sets are not disjoint, then we can't use them to compile the entry.
    4. If they are disjoint, but more than one FIRST set is nullable, again, can't compile the entry.
    5. compile a match, with each case_branch one of the rule-branches, and the pattern being the FFO set.
 *)
value compile1a_entry cg e = do {
  let loc = e.ae_loc in
  let ename = e.ae_name in
  if ((List.hd e.ae_levels).al_rules.au_rules
      |> List.exists (fun [
                          {ar_psymbols=[{ap_symb=(ASregexp _ _|ASinfer _ _)} :: _]} -> True
                        | _ -> False
     ])) then do {
      CG.add_warning cg (CG.adjust_loc cg loc) ename "compile1a_entry: single-rule entry, starts with regexp: FIRST/FOLLOW disallowed" ;
      failwith "caught"
    }
  else () ;
  let ff = CG.follow cg ename in
  let fi_fo_rule_list =
    match (List.hd e.ae_levels).al_rules.au_rules
          |> List.map (compute_fifo cg loc ff) with [
      x -> x
    | exception First.ExternalEntry eename -> do {
        CG.add_warning cg (CG.adjust_loc cg loc) eename "compile1a_entry: entry is external, FIRST/FOLLOW disallowed" ;
        failwith "caught"
      }
      ] in do {
    if not (disjoint cg loc fi_fo_rule_list) then do {
    CG.add_warning cg (CG.adjust_loc cg loc) e.ae_name "compile1_entry: FIFO sets were not disjoint" ;
    failwith "caught"
    }
    else if 1 < List.length (List.filter (fun (fi, _, _) -> Follow.nullable fi) fi_fo_rule_list) then do {
      CG.add_warning cg (CG.adjust_loc cg loc) e.ae_name "compile1a_entry: more than one branch is nullable" ;
      failwith "caught"
    }
    else () ;
    let (match_nest, fifotxt) = build_match_nest loc cg e fi_fo_rule_list in
    let matcher_name = (Name.print ename)^"_matcher" in
    let branches =
      fi_fo_rule_list
    |> List.mapi (compile1a_branch cg e) in
    let rhs =
      match branches with [
        [] -> <:expr< fun __strm__ -> raise Stream.Failure >>
      | _ ->
         let branches =
           branches
         |> List.map (fun (p,wo,e) -> (p,wo,<:expr< $e$ __strm__ >>)) in
         let branches = branches @ [
               (<:patt< _ >>, <:vala< None >>, <:expr< raise Stream.Failure >>)
             ] in
         <:expr< fun __strm__ -> match ($lid:matcher_name$ __strm__) [@llk.first_follow $str:String.escaped fifotxt$ ;] with [ $list:branches$ ] >> ]
    in
    let rhs = List.fold_right (fun p rhs -> <:expr< fun $p$ -> $rhs$ >>) e.ae_formals rhs in
    [(<:patt< $lid:Name.print ename$ >>, rhs, <:vala< [] >>)
    ;(<:patt< $lid:matcher_name$ >>, match_nest, <:vala< [] >>)
    ]
  }
}
;

value token_pattern loc = fun [
        CLS s None -> (<:patt< Some ($str:s$, _) >>, None)
      | CLS s (Some tok) -> (<:patt< Some ($str:s$, $str:String.escaped tok$) >>, None)
      | SPCL s -> (<:patt< Some ("", $str:s$) >>, None)
      | ANTI s ->
        (<:patt< Some ("ANTIQUOT", x) >>,
         Some <:expr< match Plexer.parse_antiquot x with [
                      Some (k, _) -> k = $str:s$
                      | _ -> False
                      ] >>)
  ] ;

value statename i = Printf.sprintf "q%04d" i ;

value edge_group_to_branches loc generic_is_final edges =
  let newst = snd (List.hd edges) in
  let branch_body = <:expr< $lid:(statename newst)$ lastf (ofs+1) >> in
  let toks = List.map fst edges in
  let (antis, rest) = Ppxutil.filter_split (fun [ ANTI _ -> True | _ -> False ]) toks in
  let rest_branches =
    if [] = rest then [] else
      let patt =
        let rest = rest |> List.map (fun [
                                         CLS s None -> <:patt< Some ($str:s$, _) >>
                                       | CLS s (Some tok) -> <:patt< Some ($str:s$, $str:String.escaped tok$) >>
                                       | SPCL s -> <:patt< Some ("", $str:s$) >>
                             ]) in
        List.fold_left (fun p1 p2 -> <:patt< $p1$ | $p2$ >>) (List.hd rest) (List.tl rest) in
      [(patt, <:vala< None >>, branch_body)] in

  let antis_branches =
    if [] = antis then [] else
      let kinds = antis |> List.map (fun [ ANTI s -> s ]) in
      let kinds_list_expr = 
        kinds
        |> List.map (fun s -> <:expr< $str:s$ >>)
        |> Ppxutil.convert_up_list_expr loc in
      let whene = <:expr< match Plexer.parse_antiquot x with [
                              Some (k, _) -> List.mem k $kinds_list_expr$
                            | _ -> False
                            ] >> in
      [(<:patt< Some ("ANTIQUOT", x) >>, <:vala< Some whene >>, branch_body)] in
  rest_branches @ antis_branches
;


value anti_edgegroup_to_branch loc edges =
  let newst = snd (List.hd edges) in
  let branch_body = <:expr< $lid:(statename newst)$ lastf (ofs+1) >> in
  let toks = List.map fst edges in
  let (antis, rest) = Ppxutil.filter_split (fun [ ANTI _ -> True | _ -> False ]) toks in

  let antis_branches =
    if [] = antis then [] else
      let kinds = antis |> List.map (fun [ ANTI s -> s ]) in
      let kinds_list_expr = 
        kinds
        |> List.map (fun s -> <:expr< $str:s$ >>)
        |> Ppxutil.convert_up_list_expr loc in
      let whene = <:expr< match Plexer.parse_antiquot x with [
                              Some (k, _) -> List.mem k $kinds_list_expr$
                            | _ -> False
                            ] >> in
      [(<:patt< Some ("ANTIQUOT", x) >>, <:vala< Some whene >>, branch_body)] in
  antis_branches
;

value nonanti_edge_to_branch loc generic_is_final (cls,newst) =
  let branch_body = <:expr< $lid:(statename newst)$ lastf (ofs+1) >> in
  match cls with [
    CLS s None ->
    let patt = <:patt< Some ($str:s$, _) >> in
    (patt, <:vala< None >>, branch_body)

  | CLS s (Some tok) ->
    let patt = <:patt< Some ($str:s$, $str:String.escaped tok$) >> in
    let branch_body =
      match List.assoc s generic_is_final with [
          st -> 
        <:expr< let lastf = Some (ofs, $int:string_of_int st$) in $branch_body$ >>
      | exception Not_found -> branch_body
    ] in
    (patt, <:vala< None >>, branch_body)

  | SPCL s ->
    let patt = <:patt< Some ("", $str:s$) >> in
    (patt, <:vala< None >>, branch_body)

  | ANTI _ -> assert False
  ]
;

value edges_to_branches loc states edges =
  let find_state st =
    try
      List.find (fun (i, _, _, _) -> st = i) states
    with Not_found -> failwithf "edges_to_branches internal error: state %d not found" st in
  let state_is_final st =
    let (_, _, final, _) = find_state st in
    None <> final in

  let spcl_edges = List.filter (fun [ (SPCL _, _) -> True | _ -> False ]) edges in
  let anti_edges = List.filter (fun [ (ANTI _, _) -> True | _ -> False ]) edges in
  let tokgeneric_edges = List.filter (fun [ (CLS _ None, _) -> True | _ -> False ]) edges in
  let tokspecific_edges = List.filter (fun [ (CLS _ (Some _), _) -> True | _ -> False ]) edges in

  let generic_is_final =
    tokgeneric_edges
    |> List.filter_map (fun [ (CLS ty None, st) when state_is_final st -> Some (ty, st) | _ -> None ]) in

  let spcl_branches = List.map (nonanti_edge_to_branch loc generic_is_final) spcl_edges in
  let tokgeneric_branches = List.map (nonanti_edge_to_branch loc generic_is_final) tokgeneric_edges in
  let tokspecific_branches = List.map (nonanti_edge_to_branch loc generic_is_final) tokspecific_edges in

  let anti_edge_groups = Std.nway_partition (fun (_, st) (_, st') -> st = st') anti_edges in

  let anti_branches =
    anti_edge_groups |> List.concat_map (anti_edgegroup_to_branch loc) in

  spcl_branches @ tokspecific_branches @ tokgeneric_branches @ anti_branches
;

value letrec_nest (init, initre, states) =
  let open PatternBaseToken in
  let loc = Ploc.dummy in
  let find_state st =
    try
      List.find (fun (i, _, _, _) -> st = i) states
    with Not_found -> failwithf "letrec_nest internal error: state %d not found" st in
  let state_is_final st =
    let (_, _, final, _) = find_state st in
    None <> final in
  let export_state (i, rex, final, edges) =
    let rhs =
      if edges = [] then <:expr< lastf >> else
        let generic_is_final =
          edges
        |> List.find_map (fun [ (CLS ty None, st) when state_is_final st -> Some (ty, st) | _ -> None ]) in
(*
      let branches =
        let edge_groups = Std.nway_partition (fun (_, st) (_, st') -> st = st') edges in
        edge_groups
        |> List.concat_map (edge_group_to_branches loc generic_is_final) in
 *)
      let branches = edges_to_branches loc states edges in
      let branches = branches @ [
          (<:patt< _ >>, <:vala< None >>, <:expr< lastf >>)
        ] in
      <:expr< match must_peek_nth (ofs+1) strm with [
                            $list:branches$
                          ] >> in
    match final with [
      Some (OUTPUT output) ->
      (<:patt< $lid:(statename i)$ >>, <:expr< fun lastf ofs -> let lastf = Some (ofs, $int:string_of_int output$) in $rhs$ >>, <:vala< [] >>)
    | None ->
      (<:patt< $lid:(statename i)$ >>, <:expr< fun lastf ofs -> $rhs$ >>, <:vala< [] >>)
    ] in
  let bindl = List.map export_state states in
  <:expr< fun strm ->
    let open Llk_regexps in
    let open PatternBaseToken in
    let rec $list:bindl$ in $lid:(statename init)$ None 0 >>
;

value compile1b_branch cg ename branchnum r =
  let loc = r.ar_loc in
  let body = compile1_rule cg ename r in
  (<:patt< Some (_, $int:string_of_int branchnum$ ) >>, <:vala< None >>, body)
;

value fifo_to_regexp cg e r =
  let loc = e.ae_loc in
  let ff = CG.follow cg e.ae_name in
  let (fi, ff, r) = compute_fifo cg loc ff r in
  let ffo = Follow.fifo_concat cg loc ~{if_nullable=True} fi ff in
  ffo |> List.map PSyn.token
  |> PSyn.disjunction
;

(** infer_regexp [stk] [r]

    infers the regexp for rule [r], and if this requires recursing into
    an entry already on [stk], will raise Failure
 *)
value infer_regexp loc cg e r =
  match r.ar_psymbols with [
      [ ({ap_symb=ASregexp _ rexname} as h) :: _ ] ->
      (match CG.gram_regexp cg rexname with [
           exception Not_found -> do {
             CG.add_failuref cg (CG.adjust_loc cg loc) e.ae_name "infer_regexp: undefined regexp %s" (Name.print rexname) ;
             failwith "caught"
           }
         | x -> x
      ])

    | [ ({ap_symb=ASinfer _ depth}) :: _ ] ->
       Infer.length_regexp_of_rule cg e.ae_name r depth

     | [ {ap_symb=ASnterm _ nt _ _} :: _ ] when CG.exists_external_ast cg nt ->
        CG.gram_external cg nt

    | _ ->
       fifo_to_regexp cg e r
    ]
;

value compute_branch_regexp cg e i r =
  let loc = e.ae_loc in
  let rex = infer_regexp loc cg e r in
  PSyn.(rex @@ PSyn.token (OUTPUT i))  
;

value compute_entry_regexp cg e =
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  let re_branches =
    List.mapi (compute_branch_regexp cg e) rl in
  PSyn.disjunction re_branches
;

value compute_firstk_regexp cg e =
  match CG.atn_firstk cg e.ae_name with [
      None -> compute_entry_regexp cg e
    | Some fk ->
      fk
      |> List.concat_map (fun (branchnum, tll) ->
             tll |> List.map (fun tl -> (branchnum, tl))
           )
      |> List.map (fun (branchnum, tl) ->
             let re = List.fold_left (fun re t -> PSyn.(re @@ token t)) PSyn.epsilon tl in
             PSyn.(re @@ token (OUTPUT branchnum))
           )
      |> PSyn.disjunction
    ]
;


value compile1b_entry cg e =
  let loc = e.ae_loc in
  let ename = e.ae_name in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  let fullre = compute_firstk_regexp cg e in
  let predictor =
    if PSyn.(equal zero fullre) then
      <:expr< fun __strm__ -> raise Stream.Failure >>
    else
      let module C = Compile(struct value rex = fullre ; value extra = (CG.alphabet cg); end) in
      let exported_dfa = C.BEval.OutputDfa.(export (dfa fullre)) in
      letrec_nest exported_dfa in
  let retxt = String.escaped (PSyn.print fullre) in
  let predictor_name = (Name.print ename)^"_regexp" in
  let branches = 
    rl
    |> List.mapi (compile1b_branch cg e) in
  let branches =
    branches
    |> List.map (fun (p,wo,e) -> (p,wo,<:expr< $e$ __strm__ >>)) in
  let branches = branches @ [
        (<:patt< _ >>, <:vala< None >>, <:expr< raise Stream.Failure >>)
      ] in
  let rhs =
    <:expr< fun __strm__ -> match ($lid:predictor_name$ __strm__) [@llk.regexp $str:retxt$ ;] with [
                                $list:branches$
                              ] >> in
  let rhs = List.fold_right (fun p rhs -> <:expr< fun $p$ -> $rhs$ >>) e.ae_formals rhs in
  [(<:patt< $lid:Name.print ename$ >>, rhs, <:vala< [] >>)
  ;(<:patt< $lid:predictor_name$ >>, predictor, <:vala< [] >>)
  ]
  ;
(*
value compile1_entry cg e =
  match compile1a_entry cg e with [
      exception Failure "caught" -> do {
        let locs =
          (List.hd e.ae_levels).al_rules.au_rules
          |> List.map (fun [
                           {ar_psymbols=[] ; ar_loc=loc} -> loc
                         | {ar_psymbols=[ {ap_loc=loc} :: _]} -> loc
               ]) in
        CG.add_warningf cg e.ae_loc e.ae_name "compile1_entry: FIRST/FOLLOW strategy failed\n%!%a"
               Fmt.(list string)
               (locs |> List.map (CG.adjust_loc cg) |> List.map Ploc.string_of_location) ;
        compile1b_entry cg e
      }
    | x -> x
    ]
;
  *)
value compile1_entry cg e = compile1b_entry cg e ;

value compile_sp_entry cg e = do {
  let loc = e.ae_loc in
  let ename = e.ae_name in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  let (sp_rl, nonsp_rl) = Ppxutil.filter_split S9SeparateSyntactic.is_syntactic_predicate_rule rl in
  assert (List.length nonsp_rl = 1) ;
  assert (sp_rl <> []) ;
  let fallback = match List.hd nonsp_rl with [
        {ar_psymbols = psl ; ar_action = Some _} as r ->
        <:expr< $compile1_rule cg e r$ __strm__ >>

      | _ -> assert False
      ] in
  let rhs = List.fold_right (fun r fallback ->
      match r with [
          {ar_psymbols=[{ap_loc=loc; ap_symb=ASsyntactic _ s} :: t]} ->
          let r' = {(r) with ar_psymbols = t} in
          let body = compile1_rule cg e r' in
          let spred_expr = compile1_symbol cg loc e s in
          <:expr<
            if try do { ignore ($spred_expr$ (clone_stream __strm__)) ; True }
                      with [ (Stream.Failure | Stream.Error _) -> False ] then
              $body$ __strm__
            else
              $fallback$
              >>
        | _ -> assert False
        ]
    ) sp_rl fallback in
  let rhs = <:expr< fun __strm__ -> $rhs$ >> in
  let rhs = List.fold_right (fun p rhs -> <:expr< fun $p$ -> $rhs$ >>) e.ae_formals rhs in
  [(<:patt< $lid:Name.print ename$ >>, rhs, <:vala< [] >>)]
}
;

value compile_entry cg e =
  if (List.hd e.ae_levels).al_rules.au_rules |>  List.exists S9SeparateSyntactic.is_syntactic_predicate_rule then
    compile_sp_entry cg e
  else
    compile1_entry cg e
;

value compile_entries cg el = do {
  assert ([] = CG.errors cg) ;
  let lol =
    el
    |> List.map (fun e ->
           try Some (compile_entry cg e)
           with [
               Failure "caught" -> None
             | exn ->
                let bts = Printexc.(get_raw_backtrace() |> raw_backtrace_to_string) in do {
                 CG.add_exn cg (CG.adjust_loc cg e.ae_loc) e.ae_name (bts, exn) ;
                 None
               }
         ]) in do {
    let failed = List.exists ((=) None) lol in
    if [] <> CG.errors cg then
      report_compilation_errors cg
        Fmt.(str "Compilation %s" (if failed then "FAILED" else "WARNINGS"))
    else () ;
    if failed then
      failwith "COMPILATION FAILED"
    else
      lol
      |> List.map Std.outSome
      |> List.concat
  }
}
;

value compute_follow (({gram_loc=loc; gram_exports=expl; gram_entries=el; gram_id=gid}, _) as cg) =
  try
    Follow.exec0 cg ~{tops=expl} el
  with
    [
      exn ->
      let open Printexc in
       let rbt = get_raw_backtrace() in
       let bts = (rbt |> raw_backtrace_to_string) in do {
        CG.add_exn cg Ploc.dummy (Name.mk "<all-entries>") (bts, exn) ;
        report_compilation_errors cg "FIRST/FOLLOW computation FAILED" ;
        raise_with_backtrace exn rbt
      }
    ]
;

value compile_top_entry cg e =
  let loc = e.ae_loc in
  let n = Name.print e.ae_name in
  let msg = Fmt.(str "illegal begin of %s" (Name.root e.ae_name)) in
  let rhs = <:expr< fun __strm__ ->
                    try
                      F . $n$ __strm__
                    with Stream.Failure -> raise (Stream.Error $str:msg$) >> in
  let rhs = List.fold_right (fun p rhs -> <:expr< fun $p$ -> $rhs$ >>) e.ae_formals rhs in
  (<:patt< $lid:n$ >>, rhs, <:vala< [] >>)
;
value exec (({gram_loc=loc; gram_exports=expl; gram_entries=el; gram_id=gid}, _) as cg)  =
let _ = compute_follow cg in
  let fdefs = compile_entries cg el in
  let top_defs =
    (CG.g cg).gram_exports
    |> List.map (fun n ->
           compile_top_entry cg (CG.gram_entry cg n)
         ) in
  let token_patterns =
    all_tokens el @ (
      (CG.gram_regexps cg)
      |> List.map snd
      |> List.concat_map PatternRegexp.tokens
    )
    |> List.filter (fun [ CLS _ _ | SPCL _ -> True | ANTI _ -> False])
    |> List.sort_uniq PatternBaseToken.compare
  in
  let token_actions =
    token_patterns
    |> List.map (fun [
      CLS c _ -> <:expr< lexer.tok_using ($str:c$, "") >>
    | SPCL k -> <:expr< lexer.tok_using ("", $str:k$) >>
                   ])
  in
  let token_actions = token_actions @ [ <:expr< () >> ] in
  let exported_entries =
    expl
  |> List.filter (fun ename -> not (CG.exists_external_ast cg ename))
  |> List.map (fun ename -> <:str_item< value $lid:Name.print ename$ = Grammar.Entry.of_parser gram $str:Name.print ename$ F. $lid:Name.print ename$ >>) in
  let lexer_gram = match (CG.g cg).gram_extend with [
        None -> <:str_item< declare
                     value lexer = Plexer.gmake () ;
                     value gram = Grammar.gcreate lexer ;
                  end >>
      | Some (Some li,lid) ->
                <:str_item< declare
                     value gram = $longid:Pcaml.unvala li$ . $_lid:lid$ ;
                     value lexer = Grammar.glexer gram ;
                  end >>
      | Some (None,lid) -> <:str_item< declare
                     value gram = $_lid:lid$ ;
                     value lexer = Grammar.glexer gram ;
                  end >>
      ] in

  <:str_item< module $uid:gid$ = struct
 $lexer_gram$ ;
 module F = struct
   open Pa_llk_runtime.Llk_runtime ;
   value rec $list:fdefs$ ;
 end ;
 module Top = struct
   value $list:top_defs$ ;
 end ;
 open Plexing ;
 do { $list:token_actions$ } ;
 declare $list:exported_entries$ end ;
 end >>
;
end ;

module Dump = struct

value exec msg cg = do {
  let pctxt = if Codegen.report_verbose.val then Pr.normal else Pr.errmsg in
  Codegen.dump_gram stderr cg msg ;
  cg
}
;
end ;

module Top = struct
open Parse_gram ;

value read_file = RT.read_file ;

value parse loc ?{bootstrap=False} s =
  let pa = if bootstrap then Parse_bootstrapped.pa loc else RT.pa loc in
  try
    pa s
  with [
      Ploc.Exc loc' exn ->
      let open Printexc in
      let rbt = get_raw_backtrace() in
      raise_with_backtrace (Ploc.Exc (CG.adjust0_loc loc loc') exn) rbt
    ]
;

value normre loc ?{bootstrap=False} s =
  s
  |> parse loc ~{bootstrap=bootstrap} |> CG.mk
  |> S0Alphabet.exec
  |> S1ProcessRegexps.exec
  |> CheckSyntax.exec
  |> CheckLexical.exec
;

value vala_kinds loc ?{bootstrap=False} s =
  s
  |> normre loc ~{bootstrap=bootstrap}
  |> S0ValaKinds.exec
;

value coalesce loc ?{bootstrap=False} s =
  s
  |> vala_kinds loc ~{bootstrap=bootstrap}
  |> S2Coalesce.exec
;

value precedence loc ?{bootstrap=False} s =
  s
  |> coalesce loc ~{bootstrap=bootstrap}
  |> CheckLexical.exec
  |> S3Precedence.exec
  |> CheckNoSelfNext.exec
;

value empty_entry_elim loc ?{bootstrap=False} s =
  s
  |> precedence loc ~{bootstrap=bootstrap}
  |> CheckLexical.exec
  |> CheckNoPosition.exec
  |> CheckNoLabelAssocLevel.exec
  |> S4EmptyEntryElim.exec
;

value left_factorize loc ?{bootstrap=False} s =
  s
  |> empty_entry_elim loc ~{bootstrap=bootstrap}
  |> S5LeftFactorize.exec
;

value lambda_lift loc ?{bootstrap=False} s =
  s
  |> left_factorize loc ~{bootstrap=bootstrap}
  |> CheckLexical.exec
  |> S6LambdaLift.exec
  |> CheckLexical.exec
  |> SortEntries.exec
;

value lift_lists loc ?{bootstrap=False} s =
  s
  |> lambda_lift loc ~{bootstrap=bootstrap}
  |> S7LiftLists.exec
  |> Dump.exec "After S7LiftLists"
;

value lift_left_assoc loc ?{bootstrap=False} s =
  s
  |> lift_lists loc ~{bootstrap=bootstrap}
  |> S8LiftLeftAssoc.exec
  |> Dump.exec "After S7LiftLeftAssoc"
;

value expand_macros loc ?{bootstrap=False} s =
  s
  |> lift_left_assoc loc ~{bootstrap=bootstrap}
  |> S9ExpandMacros.exec
  |> Dump.exec "After S9ExpandMacros"
;

value left_factorize2 loc ?{bootstrap=False} s =
  s
  |> expand_macros loc ~{bootstrap=bootstrap}
  |> S5LeftFactorize.exec
;

value lambda_lift2 loc ?{bootstrap=False} s =
  s
  |> left_factorize2 loc ~{bootstrap=bootstrap}
  |> CheckLexical.exec
  |> S6LambdaLift.exec
  |> CheckLexical.exec
  |> SortEntries.exec
;

value separate_syntactic loc ?{bootstrap=False} s =
  s
  |> lambda_lift2 loc ~{bootstrap=bootstrap}
  |> S9SeparateSyntactic.exec
;

value first loc ?{bootstrap=False} s =
  s
  |> separate_syntactic loc ~{bootstrap=bootstrap}
  |> First.exec
;

value follow loc ?{bootstrap=False} ~{tops} s =
  s
  |> separate_syntactic loc ~{bootstrap=bootstrap}
  |> Follow.exec1 ~{tops=tops}
;

value codegen loc ?{bootstrap=False} s =
  s
  |> separate_syntactic loc ~{bootstrap=bootstrap}
  |> SortEntries.exec
  |> Follow.exec
  |> BuildATN.exec
  |> ATNFirst.exec
  |> CheckATNFirst.exec
  |> Dump.exec "final grammar before codegen"
  |> Codegen.exec
;

end ;

Pcaml.add_option "-llk-report-verbose"
  (Arg.Unit (fun _ → Codegen.report_verbose.val := True))
  "Enable verbose reporting from the LLK parser-generator.";
