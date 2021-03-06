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

value identical l = do {
    assert (l <> []) ;
    List.for_all ((=) (List.hd l)) (List.tl l)
}
;

value entry_name e = e.ae_name ;
value entry_labels e =
  e.ae_levels
  |> List.filter_map (fun [ {al_label=Some l} -> Some l | _ -> None ]) ;

value entry_position e = e.ae_pos ;
value entry_location e = e.ae_loc ;

module Token = Llk_regexps.PatternBaseToken ;

value print_token_option = fun [
    None -> "eps"
|   Some t -> Token.print t
]
;

module Ctr = struct
  type t = ref int ;
  value mk ?{initv=0} () = ref initv ;
  value next ctr = let rv = ctr.val in do { incr ctr ; rv } ;
end ;

module StringCtr = struct
  type t = { it : Hashtbl.t string Ctr.t } ;
  value mk () = { it = Hashtbl.create 23 } ;
  value find {it=it} s =
    match Hashtbl.find it s with [
        x -> x
      | exception Not_found -> do {
          let v = Ctr.mk ~{initv=1} () in
          Hashtbl.add it s v ;
          v
        }
      ]
  ;
  value next ctr = Ctr.next ctr ;
  value fresh_name root it =
    let r = find it (fst root) in
    let n = Ctr.next r in
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


module type NODESIG = sig
  type t = 'a [@@deriving (show,eq,ord) ;];
  value print : t -> string ;
  value pp_hum : Fmt.t t ;
end ;
module type LABELSIG = sig
  type t = 'a [@@deriving (show,eq,ord) ;];
  value print : t -> string ;
  value pp_hum : Fmt.t t ;
end;

module type GRAPHSIG = sig
  module Node : NODESIG ;
  module Label : LABELSIG ;
  type t = 'a ;
  type edge_t = (Node.t * Label.t * Node.t) ;
  value mk : unit -> t ;
  value add_node : t -> Node.t -> Node.t ;
  value nodes : t -> list Node.t ;
  value add_edge : t -> edge_t -> unit ;
  value edge_labels : t -> Node.t -> list Label.t ;
  value edges : t -> Node.t -> list edge_t ;
  value traverse : t -> Node.t -> Label.t -> list Node.t ;
  value dump : out_channel -> t -> unit ;
end ;

module Graph(Node: NODESIG)(Label:LABELSIG)
  : (GRAPHSIG with module Node = Node and module Label = Label) = struct
module Node = Node ;
module Label = Label ;

type edge_t = (Node.t * Label.t * Node.t) ;
type t = {
  nodes : ref (list Node.t)
; edges: mutable list edge_t
; edges_ht: MHM.t Node.t (MHM.t Label.t (ref (list Node.t)))
} ;

value mk () =
  { nodes = ref []
  ; edges = []
  ; edges_ht = MHM.mk 23
  }
;

value add_node it n = do { Std.push it.nodes n ; n } ;
value nodes it = it.nodes.val ;

value add_edge it ((src, lab, dst) as e) = do {
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
value edges it src =
  edge_labels it src
  |> List.concat_map (fun lab ->
         traverse it src lab
         |> List.map (fun dst -> (src, lab, dst)))
;

value dump f it = do {
  let open Printf in
  let node2string n = Node.print n in
  let node2label n = Node.print n in
  let state_label q = node2label q in
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
           "circle"
       );
  (* Edges. *)
    it.edges
    |> List.iter (fun (src,lab,dst) ->
           fprintf f "%s -> %s [ label=\"%s\" ] ;\n"
             (node2string src)
             (node2string dst)
             (String.escaped (Label.print lab))
         ) ;
    fprintf f "}\n%!"
}
;
end ;

module ATN0 = struct
module Node = struct
  type t = [
      ENTER of Name.t
    | EXIT of Name.t
    | BRANCH of Name.t and int
    | IN_BRANCH of Name.t and int and int
    | BARRIER of Name.t and int
    | THEN_OPT of t
    | THEN_LIST0 of t
  ] [@@deriving (show,eq,ord) ;] ;
  value rec print = fun [
    ENTER n -> Fmt.(str "ENTER %s" (Name.print n))
  | EXIT n -> Fmt.(str "EXIT %s" (Name.print n))
  | BRANCH n i -> Fmt.(str "BRANCH %s %d" (Name.print n) i)
  | IN_BRANCH n i j -> Fmt.(str "BRANCH %s %d:%d" (Name.print n) i j)
  | BARRIER n i -> Fmt.(str "BARRIER %s %d" (Name.print n) i)
  | THEN_OPT n -> Fmt.(str "%s THEN_OPT" (print n))
  | THEN_LIST0 n -> Fmt.(str "%s THEN_LIST0" (print n))
  ] ;
  value pp_hum pps x = Fmt.(pf pps "%s" (print x)) ;
end ;

module Label = struct
  type t = [
      EPS
    | TOKEN of Token.t
    | NTERM of Name.t
    | PRED of a_symbol
    | MUTATION_BARRIER
    ] [@@deriving (show,eq,ord) ;]
  ;

  value print = fun [
      EPS -> "eps"
    | TOKEN tok -> Token.print tok
    | NTERM n -> Name.print n
    | PRED s -> Pr.(symbol ~{pctxt=errmsg} Pprintf.empty_pc s)
    | MUTATION_BARRIER -> "!!"
  ] ;
  value pp_hum pps x = Fmt.(pf pps "%s" (print x)) ;
end ;

module G = Graph(Node)(Label) ;

module Raw = struct
type t = {
  g : G.t
; entry_map : MHM.t Name.t (Node.t * Node.t)
; entry_branch_map : MHM.t (Name.t * int) Node.t
; bhole_nodes : MHS.t Node.t
; nonterm_edges_ht: MHM.t Name.t (ref (list G.edge_t))
; tokens : MHS.t Token.t
} ;

value mk () =
  { g = G.mk()
  ; tokens = MHS.mk 23
  ; entry_map = MHM.mk 23
  ; entry_branch_map = MHM.mk 23
  ; bhole_nodes = MHS.mk 23
  ; nonterm_edges_ht = MHM.mk 23
  }
;

value _add_node it n = G.add_node it.g n ;
value nodes it = G.nodes it.g ;
value tokens it = MHS.toList it.tokens ;

value new_entry it ename = do {
  assert (not (MHM.in_dom it.entry_map ename)) ;
  let snode = _add_node it (Node.ENTER ename) in
  let enode = _add_node it (Node.EXIT ename) in
  MHM.add it.entry_map (ename, (snode, enode)) ;
  (snode, enode)
}
;

value entry_nodes it ename =
 match MHM.map it.entry_map ename with [
   x -> x
 | exception Not_found -> new_entry it ename
 ]
;

value mark_bhole it n = MHS.add n it.bhole_nodes ;
value is_bhole it n = MHS.mem n it.bhole_nodes ;

value add_edge it ((src, lab, dst) as e) = do {
    (match lab with [ Label.TOKEN t -> MHS.add t it.tokens | _ -> ()]) ;
    G.add_edge it.g e ;
    (match lab with [
         Label.NTERM nt ->
         let nt_ref = match MHM.map it.nonterm_edges_ht nt with [
               x -> x
             | exception Not_found -> do {
                 let x = ref [] in 
                 MHM.add it.nonterm_edges_ht (nt, x) ;
                 x
               }
             ] in
         Std.push nt_ref e
       | _ -> ()
       ])
}
;
value edge_labels it src = G.edge_labels it.g src ;

value traverse it src lab = G.traverse it.g src lab ;

value nonterm_edges it nt =
  match MHM.map it.nonterm_edges_ht nt with [
      x -> x.val
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
  let n' = _add_node it (BRANCH ename i) in
  let edge = (snode, Label.EPS, n') in
  add_edge it edge ;
  add_entry_branch it ename i n' ;
  n'
}
;

value dump f it = G.dump f it.g ;
end ;

end ;
module Step = struct
type t = [
    TOKEN_STEP of Token.t
  | PRED_STEP of a_symbol
  ] [@@deriving (show,eq,ord) ;]
;
value print = fun [
    TOKEN_STEP t -> Token.print t
  | PRED_STEP s -> Fmt.(str "(%s)?" (Pr.(symbol ~{pctxt=errmsg} Pprintf.empty_pc s)))
]
;
value pp pps t = Fmt.(pf pps "%s" (print t)) ;
end ;

module ExportedDFA = struct
type state_t =
  {
    num : int
  ; final : list int
  ; transitions : list (Step.t * int)
  }
;
type t =
  {
    init : int
  ; states : list state_t
  }
;
end ;
module EDFA = ExportedDFA ;

module CompilingGrammar = struct
  type error_t = { loc : Ploc.t ; ename : Name.t ; kind : string ; msg : string ; backtrace : string } ;
  type mut_data_t = {
      ctr : StringCtr.t
    ; gram_alphabet : mutable list Token.t
    ; gram_regexps: mutable list (Name.t * regexp)
    ; gram_externals: mutable list (Name.t * regexp)
    ; errors : mutable list error_t
    ; atn_first: MHM.t Name.t (list Step.t)
    ; atn : mutable ATN0.Raw.t
    ; atn_dfa : MHM.t Name.t (option EDFA.t)
    ; entry_branch_regexps: MHM.t Name.t (list (int * PSyn.t))
    } ;
  type t = (Llk_types.top * mut_data_t) ;

 value fresh_name cg x = StringCtr.fresh_name x (snd cg).ctr ;

  value mk t = (t, {
                  ctr = StringCtr.mk()
                ; gram_alphabet = []
                ; gram_regexps = []
                ; gram_externals = []
                ; errors = []
                ; atn_first = MHM.mk 23
                ; atn = ATN0.Raw.mk ()
                ; atn_dfa = MHM.mk 23
                ; entry_branch_regexps = MHM.mk 23
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
  value gram_entry_opt cg nt =
    List.find_opt (fun e -> nt = e.ae_name) (g cg).gram_entries
  ;
  value gram_entry cg nt =
    match gram_entry_opt cg nt with [
        None -> assert False
      | Some e -> e
      ]
  ;

  value gram_atn cg = (snd cg).atn ;

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

  value set_atn_dfa cg ename l = MHM.add (snd cg).atn_dfa (ename, l) ;
  value atn_dfa cg ename = MHM.map (snd cg).atn_dfa ename ;

  value set_entry_branch_regexps (cg : t) ename l = MHM.add (snd cg).entry_branch_regexps (ename, l) ;
  value entry_branch_regexps (cg : t ) ename = MHM.map (snd cg).entry_branch_regexps ename ;

end ;
module CG = CompilingGrammar ;


module Dump = struct

value report_verbose = ref False ;

value dump_gram oc cg msg = do {
  Fmt.(pf stderr "================================ %s ================================\n%!" msg) ;
  let pctxt = if report_verbose.val then Pr.normal else Pr.errmsg in
  Fmt.(pf stderr "================================================================\n") ;
  (CG.gram_entries cg)
  |> List.iter (fun e ->  do {
    Fmt.(pf stderr "Entry: %s\n"
           Pr.(entry ~{pctxt=pctxt} Pprintf.empty_pc e)
    ) ;
    (match CG.atn_first cg e.ae_name with [
       fo ->
       Fmt.(pf stderr "ATN First: %a\n" (list ~{sep=const string " "} Step.pp) fo)
     | exception Not_found -> ()
     ]) ;
    (match CG.entry_branch_regexps cg e.ae_name with [
         l ->
         let pp1 pps (n,re) = Fmt.(pf pps "%s -> %d" (PSyn.print re) n) in
         Fmt.(pf stderr "Entry Branch Regexps:\n\t%a\n" (list ~{sep=const string "\n\t"} pp1) l)
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

value exec msg cg = do {
  let pctxt = if report_verbose.val then Pr.normal else Pr.errmsg in
  dump_gram stderr cg msg ;
  cg
}
;
end ;

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
      | ASoptv _ _ _ _ -> ["opt"]
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
  open Token ;
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
    List.sort_uniq Token.compare acc.val
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

value exec cg = cg |> process_regexps ;

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
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with
             Llk_migrate.migrate_a_symbol = migrate_a_symbol
           } in
  List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) (CG.gram_entries cg)
;

value mentions cg =
  let entries = ref [] in
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm _ nt _ _ as s -> do { Std.push entries nt ; s }
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with
             Llk_migrate.migrate_a_symbol = migrate_a_symbol
           } in do {
    List.iter (fun e -> ignore (dt.migrate_a_entry dt e)) (CG.gram_entries cg) ;
    entries.val
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
  let mentioned_entries = mentions cg in
  let regexp_mentioned_regexps = regexp_mentions cg in
  let unused = Std.(subtract
                      defined
                      (union exported (union mentioned_entries regexp_mentioned_regexps))) in
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
  | ASpriority _ _ -> ()
  | ASopt _ _ s -> check_symbol cg env s
  | ASoptv _ _ _ s -> check_symbol cg env s
  | ASleft_assoc _ _ s1 s2 _ ->  do { check_symbol cg env s1 ; check_symbol cg env s2 }
  | ASrules _ rs -> check_rules cg env rs
  | ASself _ _ -> ()
  | AStok _ _ _ -> ()
  | ASsemantic _ _ -> ()
  | ASsyntactic _ s -> check_symbol cg env s
  | ASmutation_barrier _ -> ()
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
  let (patt_guess,expr_guess) =
    let r = List.hd rl in
    if r.ar_action = None then (None, None)
    else
    match List.hd rl with [
        {ar_psymbols=[{ap_patt= Some <:patt< $lid:v$ >>; ap_symb=ASself _ _} :: _]} ->
        (Some <:patt< $lid:v$ >>,Some <:expr< $lid:v$ >>)
      | {ar_psymbols=[{ap_patt= Some <:patt< $lid:v$ >>; ap_symb=ASnterm _ nt _ None} :: _]} when ename = nt ->
        (Some <:patt< $lid:v$ >>,Some <:expr< $lid:v$ >>)
      | _ ->
         let x = CG.fresh_name cg (Name.mk "x") in
         let x = Name.print x in
         (Some <:patt< $lid:x$ >>, Some <:expr< $lid:x$ >>)
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
                                   ap_patt = patt_guess ;
                                   ap_symb = ASnterm loc next (formals2actuals cg eformals) None}];
                   ar_action = expr_guess } in
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
  | ASpriority _ _ as s -> s
  | ASopt loc g s -> ASopt loc g (lift_symbol cg acc e0 [] revpats s)
  | ASoptv loc g e s -> ASoptv loc g e (lift_symbol cg acc e0 [] revpats s)

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
  | ASsemantic _ _ as s -> s
  | ASmutation_barrier _ as s -> s
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


module S7LiftListsFully = struct
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

module S7ExpandListsPartially = struct
  (** Expand all but OPT_SEP lists into simpler forms that only
      use LIST0 and OPT

   LIST0 sym -> [UNCHANGED]

================================================================

   LIST0 sym SEP sym2 ->

   OPT [ y = LIST1 sym SEP sym2 -> y ]

================================================================

   LIST1 sym ->

   [ x = sym ; y = LIST0 sym -> [x :: y] ]

================================================================

   LIST1 sym SEP sym2 ->

   [ x = sym ; y = LIST0 [ sym2 ; y = sym -> y ] -> [x :: y] ]

================================================================

   LIST0 sym SEP sym2 OPT_SEP ->

   LIST1 sym SEP sym2 OPT_SEP ->

   use same code as S7LiftListsFully

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

(**
================================================================

   LIST1 sym ->

   [ x = sym ; y = LIST0 sym -> [x :: y] ]

================================================================
 *)
value list1_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_1 s0 None as s ->
  let new_x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let new_y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let s' = ASlist loc g LML_0 s0 None in
  let rule0 = {ar_loc = loc ; ar_action = Some <:expr< [$lid:new_x$ :: $lid:new_y$] >> ;
               ar_psymbols = [{ap_loc=loc;ap_patt= Some <:patt< $lid:new_x$ >>; ap_symb=s0}
                             ;{ap_loc=loc;ap_patt= Some <:patt< $lid:new_y$ >>
                               ;ap_symb=s'}]} in
  let rl = {au_loc=loc; au_rules=[rule0]} in
  ASrules loc rl
]
;

(**
================================================================

   LIST1 sym SEP sym2 ->

   [ x = sym ; y = LIST0 [ sym2 ; y' = sym -> y' ] -> [x :: y] ]

================================================================
 *)
value list1sep_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_1 sym (Some (sep, False)) as s ->
  let ename = CG.fresh_name cg e.ae_name in
  let x = Name.print (CG.fresh_name cg (Name.mk "x")) in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let y' = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let rl =
    { au_loc = loc
    ; au_rules = [
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
                                                         ; ap_patt = Some <:patt< $lid:y'$ >>
                                                         ; ap_symb = sym
                                                       }]
                                                     ; ar_action = Some <:expr< $lid:y'$ >>}]})
                          None
          }]
        ; ar_action = Some <:expr< [$lid:x$ :: $lid:y$] >>
        }
    ]} in
  ASrules loc rl
]
;

(**
================================================================

   LIST0 sym SEP sym2 ->

   OPTV [] [ y = LIST1 sym SEP sym2 -> y ]

================================================================
 *)
value list0sep_e (cg : CG.t) (formals, actuals) e = fun [
  ASlist loc g LML_0 sym (Some (sep, False)) as s ->
  let ename = CG.fresh_name cg e.ae_name in
  let y = Name.print (CG.fresh_name cg (Name.mk "y")) in
  let prio_psl = if g then [{ap_loc=loc; ap_patt=None; ap_symb=ASpriority loc 1}] else [] in
  let rl = {
      au_loc = loc
    ; au_rules =
        [{ ar_loc = loc
         ; ar_psymbols = [
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
    } in
  ASoptv loc g <:expr< [] >> (ASrules loc rl)
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
        ASlist loc g LML_0 s0 None as s -> fallback_migrate_a_symbol dt s

      | ASlist loc g LML_1 s0 None as s ->
        let formals = dt.aux in
        let freevars = free_lids_of_a_symbol s0 in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_s = list1_e cg (formals, actuals) e s in
        migrate_a_symbol dt new_s

      | ASlist loc g LML_1 s0 (Some (s1, False)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_s = list1sep_e cg (formals, actuals) e s in
        migrate_a_symbol dt new_s

      | ASlist loc g LML_0 s0 (Some (s1, False)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_s = list0sep_e cg (formals, actuals) e s in
        migrate_a_symbol dt new_s


      | ASlist loc g LML_1 s0 (Some (s1, True)) as s ->
        let formals = dt.aux in
        let freevars = Std.union (free_lids_of_a_symbol s0) (free_lids_of_a_symbol s1) in
        let formals =
          formals
          |> List.filter (fun p -> [] <> Std.intersect (free_lids_of_patt p) freevars) in
        let actuals = formals2actuals cg formals in

        let new_e = S7LiftListsFully.list1sep_opt_e cg (formals, actuals) e s in

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

        let new_e = S7LiftListsFully.list0sep_opt_e cg (formals, actuals) e s in

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
  [ [ x = LEFT_ASSOC e3 e7 WITH f ??? x ] ]
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
                  [{ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1}
                  ;{ ap_loc = loc
                   ; ap_patt = Some <:patt< $lid:x$ >>
                   ; ap_symb = ASanti loc anti_kinds}];
                ar_action = Some <:expr< $lid:x$ >>}]}

      | ASflag loc g sym ->
         let sym = dt.migrate_a_symbol dt sym in
         let prio_ps = {ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1} in
         let prio_psl = if g then [prio_ps] else [] in
         ASrules loc
           {au_loc = loc;
            au_rules =
              [{ ar_loc = loc
               ; ar_psymbols =
                   prio_psl@[{ ap_loc = loc; ap_patt = None
                      ; ap_symb = sym
                   }]
               ; ar_action = Some <:expr< True >>}
               ;{ ar_loc = loc
                ; ar_psymbols = []
                ; ar_action = Some <:expr< False >>}]}

      | ASopt loc g sym ->
         let sym = dt.migrate_a_symbol dt sym in
         let prio_ps = {ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1} in
         let prio_psl = if g then [prio_ps] else [] in
         let x = Name.print (CG.fresh_name cg (Name.mk "x")) in

         ASrules loc
                 {au_loc = loc;
                  au_rules =
                   [{ar_loc = loc;
                     ar_psymbols =
                       prio_psl@[{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>;
                        ap_symb = sym}];
                     ar_action = Some <:expr< Some $lid:x$ >>};
                    {ar_loc = loc; ar_psymbols = [];
                     ar_action = Some <:expr< None >>}]}

      | ASoptv loc g nulle sym ->
         let sym = dt.migrate_a_symbol dt sym in
         let prio_ps = {ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1} in
         let prio_psl = if g then [prio_ps] else [] in
         let x = Name.print (CG.fresh_name cg (Name.mk "x")) in

         ASrules loc
                 {au_loc = loc;
                  au_rules =
                   [{ar_loc = loc;
                     ar_psymbols =
                       prio_psl@[{ap_loc = loc; ap_patt = Some <:patt< $lid:x$ >>;
                        ap_symb = sym}];
                     ar_action = Some <:expr< $lid:x$ >>};
                    {ar_loc = loc; ar_psymbols = [];
                     ar_action = Some nulle}]}

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

module S9ExpandFlagVala = struct

open FreeLids ;

(** expand_flag_vala

    expand FLAG and V (leave OPT alone)
 *)

value expand_flag_vala (cg : CG.t) e =
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
                  [{ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1}
                  ;{ ap_loc = loc
                   ; ap_patt = Some <:patt< $lid:x$ >>
                   ; ap_symb = ASanti loc anti_kinds}];
                ar_action = Some <:expr< $lid:x$ >>}]}

      | ASflag loc g sym ->
         let sym = dt.migrate_a_symbol dt sym in
         let prio_ps = {ap_loc=loc; ap_patt=None; ap_symb = ASpriority loc 1} in
         let prio_psl = if g then [prio_ps] else [] in
         ASrules loc
           {au_loc = loc;
            au_rules =
              [{ ar_loc = loc
               ; ar_psymbols =
                   prio_psl@[{ ap_loc = loc; ap_patt = None
                      ; ap_symb = sym
                   }]
               ; ar_action = Some <:expr< True >>}
               ;{ ar_loc = loc
                ; ar_psymbols = []
                ; ar_action = Some <:expr< False >>}]}

      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = {(dt) with
             migrate_a_symbol = migrate_a_symbol
           } in
  dt.migrate_a_entry dt e
;

value exec0 cg el = List.map (expand_flag_vala cg) el ;

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

value find_empty_entry cg el =
  el |> List.find_map (fun e ->
      let ename = e.ae_name in
      let formals = e.ae_formals in
      if Name.is_generated e.ae_name && 1 = List.length e.ae_levels then
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

module S10UnitEntryElim = struct

value unit_entry (cg : CG.t) ename =
  if not (CG.exists_entry cg ename) then None else
  let e = CG.gram_entry cg ename in
  match (List.hd e.ae_levels).al_rules.au_rules with [
      [{ar_psymbols=[{ap_patt=patt; ap_symb=ASnterm _ nt actuals None}]; ar_action = action}] ->
      if List.length e.ae_formals = List.length actuals
         && List.for_all2 (fun formal actual ->
                match (formal, actual) with [
                    (<:patt< $lid:pv$ >>, <:expr< $lid:ev$ >>) when pv = ev -> True
                  | _ -> False
              ]) e.ae_formals actuals
         && (match (patt, action) with [
                 (Some <:patt< $lid:pv$ >>, Some <:expr< $lid:ev$ >>) when pv = ev -> True
               | (None, None) -> True
               | _ -> False
            ]) then
        Some nt
      else None
    | _ -> None
    ]
;

value rec furthest_unit_entry cg ename =
  match unit_entry cg ename with [
      None -> None
    | Some nt ->
       (match furthest_unit_entry cg nt with [
            None -> Some nt
          | Some nt' -> Some nt'
       ])
    ]
;

value eliminate_unit_entry_symbols changed (cg : CG.t) e =
  let dt = Llk_migrate.make_dt () in
  let fallback_migrate_a_symbol = dt.migrate_a_symbol in
  let migrate_a_symbol dt = fun [
        ASnterm loc nt actuals None as s when Name.is_generated nt ->
        (match furthest_unit_entry cg nt with [
             None -> s
           | Some nt' -> do { changed.val := True ; ASnterm loc nt' actuals None }
           ])
      | s -> fallback_migrate_a_symbol dt s
      ] in
  let dt = { (dt) with Llk_migrate.migrate_a_symbol = migrate_a_symbol } in
  dt.migrate_a_entry dt e
;

value eliminate1 cg =
  let changed = ref False in
  let el = List.map (eliminate_unit_entry_symbols changed cg) (CG.gram_entries cg) in
  (changed.val, CG.withg cg {(CG.g cg) with gram_entries = el })
;

value rec eliminate cg =
  let (changed, cg) = eliminate1 cg in
  if changed then eliminate cg else cg
;

value eliminate_unused1 mentioned_entries cg =
  let changed = ref False in
  let reject_unmentioned e =
    if List.mem e.ae_name mentioned_entries then True
    else do { changed.val := True ; False } in
  let el = Std.filter reject_unmentioned (CG.gram_entries cg) in
  (changed.val, CG.withg cg {(CG.g cg) with gram_entries = el })
;

value rec eliminate_unused cg =
  let mentioned_entries = CheckSyntax.mentions cg in
  let mentioned_entries = mentioned_entries @ (CG.g cg).gram_exports in
  let (changed, cg) = eliminate_unused1 mentioned_entries cg in
  if changed then eliminate_unused cg else cg
;

value exec cg = cg |> eliminate |> eliminate_unused ;

end ;

module CheckLeftRecursion = struct

type null_t = [ NULLABLE | NONNULL | EMPTY ] [@@deriving (show,eq,ord) ;];

value define_nullable_entry (nullmap : MHM.t Name.t (option null_t)) ename defval =
  match MHM.map nullmap ename with [
      None -> MHM.remap nullmap ename (Some defval)
    | Some oldval when defval = oldval -> ()
    | Some oldval ->
       Fmt.(failwithf "CheckLeftRecursion: entry %s was deduced as both %a and %a"
              (Name.print ename) pp_null_t oldval pp_null_t defval)
    ]
;

value compute1_nullable_symbol nullmap s =
  let rec crec = fun [
        ASflag _ _ _ 
      | ASlist _ _ _ _ _
      | ASopt _ _ _
      | ASoptv _ _ _ _
      | ASleft_assoc _ _ _ _ _
      | ASrules _ _
      | ASself _ _
      | ASnext _ _
      | ASvala _ _ _ -> assert False

      | ASsyntactic _ _
      | ASsemantic _ _
      | ASmutation_barrier _
      | ASpriority _ _ -> Some NULLABLE

      | ASkeyw _ _ -> Some NONNULL
      | ASnterm _ nt _ _ -> MHM.map nullmap nt
      | AStok _ _ _ -> Some NONNULL
      | ASanti _ _ -> Some NONNULL
      ]
  in crec s
;

value rec compute1_nullable_psymbols nullmap = fun [
  [] -> Some NULLABLE
| [h :: t] ->
   let h_ans = compute1_nullable_symbol nullmap h.ap_symb in
   let t_ans = compute1_nullable_psymbols nullmap t in
   (match (h_ans, t_ans) with [
        (Some NULLABLE, Some NULLABLE) -> Some NULLABLE
      | (Some NONNULL, _) -> Some NONNULL
      | (_, Some NONNULL) -> Some NONNULL
      | (Some EMPTY, _) -> Some EMPTY
      | (_, Some EMPTY) -> Some EMPTY
      | _ -> None
   ])
]
;
value compute1_nullable_rule nullmap r =
  compute1_nullable_psymbols nullmap r.ar_psymbols ;

value compute1_nullable_entry nullmap e =
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  if rl = [] then ()
  else
  let per_rule = List.map (compute1_nullable_rule nullmap) rl in
  let ans =
    List.fold_left (fun a b ->
        match (a,b) with [
            (_, Some NULLABLE) -> Some NULLABLE
          | (Some NULLABLE, _) -> Some NULLABLE
          | (None, _) -> None
          | (_, None) -> None
          | (Some NONNULL, Some NONNULL) -> Some NONNULL
          | (Some EMPTY, v) -> v
          | (v, Some EMPTY) -> v
      ])
      (List.hd per_rule) (List.tl per_rule) in
  match ans with [
      None -> ()
    | Some v -> define_nullable_entry nullmap e.ae_name v
    ]
;

value compute1_nullable nullmap el =
  List.iter (compute1_nullable_entry nullmap) el ;


value rec compute_nullable_fixpoint nullmap el = do {
    let pre = List.stable_sort Stdlib.compare (MHM.toList nullmap) in
    compute1_nullable nullmap el ;
    let post = List.stable_sort Stdlib.compare (MHM.toList nullmap) in
    if pre = post then ()
    else
      compute_nullable_fixpoint nullmap el
}
;

(** Compute the set of nullable entries

    (1) for external entries, they're nullable if their regexps accept [eps].

    (2) for normal entries, we compute nullability structurally, using
        three-state logic: nullable, not-nullable, not-known.

    (3) Initially, all entries are not-known.
 *)
value compute_nullable cg = do {
  let nullmap = MHM.mk 23 in
  (CG.gram_entries cg)
  |> List.iter (fun e ->
     MHM.add nullmap (e.ae_name, None)) ;
  (CG.gram_externals cg)
  |> List.iter (fun (ename, rex) ->
         let module C = Compile(struct value rex = rex ; value extra = (CG.alphabet cg); end) in
         let is_nullable = C.BEval.nullable rex in
         let v = if is_nullable then NULLABLE else NONNULL in
         MHM.add nullmap (ename, Some v)) ;
  compute_nullable_fixpoint nullmap (CG.gram_entries cg) ;
  nullmap
}
;

value left_reaches_symbol = fun [
        ASflag _ _ _ 
      | ASlist _ _ _ _ _
      | ASopt _ _ _
      | ASoptv _ _ _ _
      | ASleft_assoc _ _ _ _ _
      | ASrules _ _
      | ASself _ _
      | ASnext _ _
      | ASvala _ _ _ -> assert False

      | ASsyntactic _ _
      | ASsemantic _ _
      | ASmutation_barrier _
      | ASpriority _ _ -> []

      | ASkeyw _ _ -> []
      | ASnterm _ nt _ _ -> [nt]
      | AStok _ _ _ -> []
      | ASanti _ _ -> []
]
;

value rec left_reaches_psymbols nullmap = fun [
  [] -> []
| [h :: t] ->
   let h_reaches = left_reaches_symbol h.ap_symb in
   h_reaches @
     (if Some NULLABLE = compute1_nullable_symbol nullmap h.ap_symb then
        left_reaches_psymbols nullmap t
      else [])
]
;
value left_reaches_rule nullmap rule =
  left_reaches_psymbols nullmap rule.ar_psymbols ;

value left_reaches_entry nullmap e =
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  List.concat_map (left_reaches_rule nullmap) rl |> List.sort_uniq Name.compare
;

value compute_left_reaches nullmap cg = do {
    let m = MHM.mk 23 in
    (CG.gram_entries cg)
    |> List.iter (fun e ->
           let l = left_reaches_entry nullmap e in
           MHM.add m (e.ae_name, l)) ;
    m
}
;

value rec left_recursive_path acc lrmap ename stk nt =
  if ename = nt then do {
    Std.push acc [nt :: stk] ;
    failwith "caught"
  }
  else
  let stk = [nt :: stk] in
  let l = match MHM.map lrmap nt with [ x -> x | exception Not_found -> [] ] in
  List.iter (left_recursive_path acc lrmap ename stk) l
;

value check_left_recursive_entry acc lrmap e =
  try
    let l = match MHM.map lrmap e.ae_name with [ x -> x | exception Not_found -> [] ] in
    List.iter (left_recursive_path acc lrmap e.ae_name [e.ae_name]) l
  with
    Failure _ -> () 
;

value compute_left_recursives lrmap cg = do {
    let acc = ref [] in
    (CG.gram_entries cg)
    |> List.iter (check_left_recursive_entry acc lrmap) ;
    List.stable_sort Stdlib.compare acc.val
}
;

value exec cg = do {
    let nullmap = compute_nullable cg in
    let lrmap = compute_left_reaches nullmap cg in
    let l = compute_left_recursives lrmap cg in
    if l <> [] then do {
      Fmt.(pf stderr "Left Recursive entries found:\n");
      l |> List.iter (fun path ->
               Fmt.(pf stderr "  [%a]\n" (list ~{sep=const string " -> "} Name.pp) path)) ;
      Fmt.(pf stderr "%!") ;
    }
    else ();
    cg ;
}
;

end ;


(** Build the ATN First/Follow/First(k) sets this grammar
*)

module ATN = struct
open Token ;
include ATN0 ;

module Build = struct
value rec symbol it (snode, enode) = fun [

    ASkeyw _ tok -> Raw.add_edge it (snode, Label.TOKEN (SPCL tok), enode)
  | ASnterm _ nt _ None -> Raw.add_edge it (snode, Label.NTERM nt, enode)

  | ASpriority _ _
    -> Raw.add_edge it (snode, Label.EPS, enode)

  | ASsyntactic _ _ as s
    -> Raw.add_edge it (snode, Label.PRED s, enode)
  | ASsemantic _ _ as s
    -> Raw.add_edge it (snode, Label.PRED s, enode)

  | ASmutation_barrier _ ->
     Raw.add_edge it (snode, Label.MUTATION_BARRIER, enode)

  | ASopt _ _ s
  | ASoptv _ _ _ s -> do {
     let optnode = Node.THEN_OPT snode in
     Raw.add_edge it (snode, Label.EPS, optnode) ;
     Raw.add_edge it (optnode, Label.EPS, enode) ;
     symbol it (optnode, enode) s
  }

  | ASlist _ _ LML_0 s None -> do {
     let listnode = Node.THEN_LIST0 snode in
     Raw.add_edge it (snode, Label.EPS, listnode) ;
     Raw.add_edge it (listnode, Label.EPS, enode) ;
     symbol it (listnode, listnode) s
    }

  | AStok _ cls tokopt ->
    Raw.add_edge it (snode, Label.TOKEN (CLS cls tokopt), enode)

  | ASanti _ anti_kinds ->
    let l = anti_kinds |> List.concat_map (fun s -> [(ANTI s); (ANTI ("_"^s))]) in
    l |> List.iter (fun tok ->
        Raw.add_edge it (snode, Label.TOKEN tok, enode))

  | ASflag _ _ _
  | ASlist _ _ _ _ _
  | ASnext _ _
  | ASnterm _ _ _ (Some _)
  | ASrules _ _
  | ASself _ _
  | ASvala _ _ _
  | ASleft_assoc _ _ _ _ _

  -> assert False

  ]
;

value rec psymbols it (e, bnum) i (snode, enode) = fun [
  [] -> Raw.add_edge it (snode, Label.EPS, enode)
| [h] -> symbol it (snode, enode) h.ap_symb
| [h :: t] -> do {
    let mid = Raw._add_node it (Node.IN_BRANCH e.ae_name bnum i) in
    symbol it (snode, mid) h.ap_symb ;
    psymbols it (e, bnum) (i+1) (mid, enode) t
  }
]
;

value rule it e (snode, enode) bnum r =
  psymbols it (e, bnum) 1 (snode, enode) r.ar_psymbols ;

value entry it e =
  let (e_snode, e_enode) = Raw.entry_nodes it e.ae_name in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  rl
  |> List.iteri (fun i r ->
         let r_snode = Raw.start_entry_branch it e.ae_name i in
         rule it e (r_snode, e_enode) i r
       )
;

value external_entry cg it (ename, rex) =
  let (snode, enode) = Raw.entry_nodes it ename in
  let module C = Compile(struct value rex = rex ; value extra = (CG.alphabet cg); end) in
  let is_nullable = C.BEval.nullable rex in
  let nulls = if is_nullable then [None] else [] in
  let toks = List.map (fun x -> Some x) (C.BEval.OutputDfa.first_tokens rex) in
  (toks@nulls)
  |> List.iteri (fun i -> fun [
    Some tok ->
    let n' = Raw._add_node it (Node.BARRIER ename i) in do {
      Raw.add_edge it (snode, Label.TOKEN tok, n') ;
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
                  let enode' = Raw._add_node it (Node.BARRIER ename (-1)) in
                  Raw.mark_bhole it enode' ;
                  Raw.add_edge it (enode, Label.TOKEN (CLS "EOI" None), enode')
                }
       ) ;
  (CG.gram_externals cg) |> List.iter (external_entry cg it)
}
;
end ;

(** NOTES ON TYPES

    A state of the ATN is always a "node" of the graph.  But a
    "configuration" is a state plus a possibly-empty stack of states,
    and it is with these configurations that we work from here down
    unless otherwise specified.

 *)

module CFG = struct
type t = {state: Node.t; stack: list Node.t; mutated: bool} [@@deriving (show,eq,ord) ;] ;
value pp_hum pps t = Fmt.(pf pps "%s[%a]"
                            (if t.mutated then "<mut>" else "")
                            (list ~{sep=const string " "} Node.pp_hum) [t.state::t.stack]) ;
value print x = Fmt.(str "%a" pp_hum x) ;
end ;
module NFACFG = struct
type t = { branchnum : int ; priority : int ; cfgs : list CFG.t }
           [@@deriving (show,eq,ord) ;] ;
value branchnum p = p.branchnum ;
value priority p = p.priority ;
value cfgs p = p.cfgs ;
value canon t = {(t) with cfgs = List.sort_uniq CFG.compare t.cfgs } ;
value canon_list l = List.sort_uniq compare (List.map canon l) ;
value eq_branchnum h h' = 
  h.branchnum = h'.branchnum
;
value eq_branchprio h h' = 
  h.branchnum = h'.branchnum
  && h.priority = h'.priority
;
value concat = fun [
  [] -> assert False
| [h :: t] as l -> do {
    assert (List.for_all (eq_branchprio h) t) ;
    canon {(h) with cfgs = l |> List.concat_map cfgs }
  }
]
; 

value branchnum_partition_then_concat (l : list t) = do {
  let ll =
    l
    |> Std.nway_partition (fun p1 p2 -> p1.branchnum = p2.branchnum) in
  assert(List.for_all (fun l -> identical (List.map priority l)) ll) ;
  List.map concat ll
}
;
end ;

module type DFA_STATE_SIG = sig
  type t = 'b ;
  value mk_dfa : list NFACFG.t -> t ;
  type state_t = 'a [@@deriving (show,eq,ord) ;] ;
  value initial : t -> state_t ;
  value is_initial: t -> state_t -> bool ;
  value extend_dfa : t -> state_t -> (Step.t * list NFACFG.t) -> (bool * state_t * list NFACFG.t);
  value prefix : string ;
end ;

module BuildDFA(S : DFA_STATE_SIG) = struct
module S = S ;
module StateCFG = struct
type _t 'a = { dfastate : 'a ; nfacfgs : list NFACFG.t } [@@deriving (show,eq,ord) ;] ;
type t = _t S.state_t [@@deriving (show,eq,ord) ;] ;
type next_t = _t (S.state_t * Step.t) [@@deriving (show,eq,ord) ;] ;

value dfastate t = t.dfastate ;
value nfacfgs t = t.nfacfgs ;
value mk st l = do {
    assert (Std.distinct (List.map NFACFG.branchnum l)) ;
    {dfastate = st; nfacfgs = NFACFG.canon_list l}
}
;
end ;
module SCFG = StateCFG ;

(** closure cg [cfgs]

    computes the set of configurations reachable from the argument set of
    configurations by only epsilon-transitions, but also by entering subsidiary
    nonterminals or by exiting to surrounding/subsequent nonterminals.

    closure is always given a set of configurations and returns a set (b/c
    this way we minimize excess work.  the result always includes the argument.

    Algorithm:

    For each cfg in the work-list:

      If the cfg.state is an EXIT-state and the cfg.stack is nonempty, then pop a state
      -- this is the next configuration

      get all edge-labels outbound from cfg.state:

        for an EPS edge-label, all dst states are added to worklist

        for a NONTERM edge-label, get all dst-states; get the start-state of the nonterm's
        ATN.  next configurations are to enter that ATN, stacking each dst-state.
 *)

value max_recursion_depth = ref 2 ;

value exceeds_recursion_depth cfg =
  let open CFG in
  let l = [cfg.state :: cfg.stack] in
  let l = List.stable_sort Node.compare l in
  let rec countrec n l =
    n > max_recursion_depth.val ||
      match l with [
          [x ; y :: t] ->
          if Node.equal x y then
            countrec (n+1) [y :: t]
          else countrec 1 [y :: t]
        | [_] | [] -> False
      ] in
  countrec 0 l
;

value has_steppable_edge (cg : CG.t) = fun [
  {CFG.state=Node.EXIT _; stack=[_ :: _]} -> False
| {state=n} ->
  n
  |> Raw.edge_labels (CG.gram_atn cg)
  |> List.exists (fun [ Label.TOKEN _ | PRED _ -> True | _ -> False ])
]
;

value watch_clrec1 (x : CFG.t) = () ;
value closure0 loc (cg : CG.t) cfg =
  let open CFG in
  let acc = ref [cfg] in
  let bad = ref [] in
  let rec clrec0 = fun [
        {state=Node.EXIT _; stack=[h::t]} as c ->
        clrec1 {(c) with state=h; stack=t}
      | {state=Node.EXIT nt; stack=[]} as c ->
         let l = Raw.nonterm_edges (CG.gram_atn cg) nt in
         l |> List.iter (fun (_, _, dst) ->
                  clrec1 {(c) with state=dst; stack=[]})
      | {state=n;stack=stk} as c ->
         let labs = Raw.edge_labels (CG.gram_atn cg) n in
         labs |> List.iter (fun [
             Label.EPS as lab ->
             let dsts = Raw.traverse (CG.gram_atn cg) n lab in
             dsts |> List.iter (fun dst -> clrec1 {(c) with state=dst})

           | MUTATION_BARRIER as lab ->
             let dsts = Raw.traverse (CG.gram_atn cg) n lab in
             dsts |> List.iter (fun dst -> clrec1 {(c) with state=dst; mutated=True})

           | TOKEN _ | PRED _ -> ()
           | NTERM nt as lab ->
              let (snode, _) = Raw.entry_nodes (CG.gram_atn cg) nt in
              let dsts = Raw.traverse (CG.gram_atn cg) n lab in
              dsts |> List.iter (fun [
                  Node.EXIT _ -> clrec1 {(c) with state=snode}
                | dst -> clrec1 {(c) with state=snode; stack=[dst :: stk]}
                ])
           ])
      ]
  and clrec1 cfg = do { watch_clrec1 cfg ; clrec1' cfg }
  and clrec1' cfg =
    if List.mem cfg bad.val then ()
    else if exceeds_recursion_depth cfg then do {
      let loc = CG.adjust_loc cg loc in
      Fmt.(pf stderr "%s: %s.ATN.closure: configuration exceeds recursion: %a\n%!"
             (Ploc.string_of_location loc)
             S.prefix
             CFG.pp_hum cfg) ;
      Std.push bad cfg
    }
    else if not (List.mem cfg acc.val) then do {
      Std.push acc cfg;
      clrec0 cfg
    }
    else ()
  in do {
    clrec0 cfg ;
    acc.val |> List.filter (fun cfg ->
    has_steppable_edge cg cfg
    || Raw.is_bhole (CG.gram_atn cg) cfg.state)
  }
;

module Memo = struct
type t = {
    closure0 : MHM.t CFG.t (list CFG.t)
  }
;
value mk () = {
    closure0 = MHM.mk 23
  }
;
end;

type cg_memo_t = (CG.t * Memo.t) ;

value memo_closure0 loc (cg, memo) cfg =
  match MHM.map memo.Memo.closure0 cfg with [
      x -> x
    | exception Not_found -> do {
        let cfgs = closure0 loc cg cfg in
        MHM.add memo.Memo.closure0 (cfg, cfgs) ;
        cfgs
      }
    ]
;

value closure loc (cg,memo) cfgs =
  cfgs
  |> List.concat_map (memo_closure0 loc (cg,memo))
  |> List.sort_uniq CFG.compare
;

(** step1 [it,ec] [st]:

    From state [st], take one non-epsilon step in the ATN
    returning the list of (tok * st) that are reached.

    NOTE WELL: this assumes that (epsilon-)[closure] will
    be performed prior to [step1]
 *)

value step1 loc ((cg,memo) : cg_memo_t) cfg = do {
  let st = cfg.CFG.state in
  let it = CG.gram_atn cg in
  if Raw.is_bhole it st then
    raise_failwithf (CG.adjust_loc cg loc)
      "ATN.step1: cannot explore tokens forward from bhole node: %s" (Node.print st)
  else () ;
  let labs = Raw.edge_labels it st in
  labs
  |> List.concat_map (fun [
       Label.EPS|NTERM _ -> []
    | (TOKEN tok) as lab ->
       let dsts = Raw.traverse it st lab in
       dsts |> List.map (fun dst -> (Step.TOKEN_STEP tok, dst))
    | (PRED s) as lab ->
       if cfg.CFG.mutated then
         raise_failwithf (CG.adjust_loc cg loc)
           "ATN.step1: cannot explore predicates past a mutation barrier:\n %a"
           CFG.pp cfg
       else
         let dsts = Raw.traverse it st lab in
         dsts |> List.map (fun dst -> (Step.PRED_STEP s, dst))
    ])
}
;

value step1_cfg loc cg cfg =
  let token_state'_list = step1 loc cg cfg in
  token_state'_list |> List.map (fun (tok, n) -> (tok,{(cfg) with state=n}))
;

value nfacfg_closure loc cg t =
  let open NFACFG in
  {(t) with cfgs = closure loc cg t.cfgs}
;

value scfg_closure loc cg t =
  let nfacfgs = t.SCFG.nfacfgs in
  let nfacfgs = List.map (nfacfg_closure loc cg) nfacfgs in
  SCFG.mk t.SCFG.dfastate nfacfgs
;

(** extend1 loc cg [t]

    [t] is an NFACFG: extend it by one token.

    1. apply [closure]: this produces more cfgs.
    2. for each [cfg], apply step1, producing pairs of (token * state).
    3. combine each pair with the original [cfg] to produce a [list (token * NFACFG)]
       each with a single [cfg]
    4. partition by [tok]
    5. merge NFACFGs.

 *)
value extend1 loc cg (t : NFACFG.t) =
  let open NFACFG in
  t.cfgs
  |> List.concat_map (fun cfg ->
         let token_cfg_list = step1_cfg loc cg cfg in
         token_cfg_list |> List.map (fun (tok, cfg) ->
                               let t' = {(t) with cfgs = [cfg]} in
                               (tok, t'))
       )
  |> Std.nway_partition (fun (tok1,_) (tok2,_) -> tok1=tok2)
  |> List.map (fun l ->
         let (tok,_) = List.hd l in
         (tok, NFACFG.(nfacfg_closure loc cg (concat (List.map snd l)))))
;


(** a [SCFG._t] is ambiguous if its [NFACFG.t]s do not have distinct priorities.
 *)
value ambiguous_scfg__t (t : SCFG._t 'a) =
  let l = t.SCFG.nfacfgs in
  not (Std.distinct (List.map NFACFG.priority l))
;

value ambiguous_scfg_next_t (t : SCFG.next_t) = ambiguous_scfg__t t ;

(** a [SCFG.t] is ambiguous if it is ambiguous as an [SCFG._t], or its
    dfastate [is_initial]
 *)
value ambiguous_scfg dfa (t : SCFG.t) =
  ambiguous_scfg__t t
(*
  || (S.is_initial dfa t.SCFG.dfastate && List.length t.SCFG.nfacfgs > 1)
 *)
;

(** extend_branches1:

  (1) use [extend1] to extend each NFACFG.t, producing a [list (tok, NFACFG.t)]
  (2) concat all lists
  (3) partition by tok
  (4) this yields a list of NFACFG.t with same token:
      partition by eq_branchnum and concat
  (5) This yields [list (tok, list NFACFG.t)] where the inner list has distinct branchnum.
  (6) Now add in the dfa-state to produce SCFG.next_t
 *)
value extend_branches1 loc (cg_memo : cg_memo_t) dfa (t : SCFG.t) : (list SCFG.t * list SCFG.t) = do {
  let open SCFG in
  let open NFACFG in
  assert (ambiguous_scfg dfa t) ;
  let next_l : list (Step.t * NFACFG.t) = t.SCFG.nfacfgs |> List.concat_map (extend1 loc cg_memo) in
  let token_partitions : list (list (Step.t * NFACFG.t)) =
    Std.nway_partition (fun (tok1,_) (tok2,_) -> tok1=tok2) next_l in
  let token_nfacfgs_list : list (Step.t * list NFACFG.t) =
    token_partitions
    |> List.map (fun l ->
           let tok = fst (List.hd l) in
           let nfacfgs = List.map snd l in
           let nfacfgs = NFACFG.branchnum_partition_then_concat nfacfgs in
           (tok, nfacfgs)) in
  let scfgs =
    token_nfacfgs_list
    |> List.map (fun (tok,nfacfgs) -> SCFG.mk (t.dfastate, tok) nfacfgs) in
  let (ambig, ok) = Ppxutil.filter_split ambiguous_scfg_next_t scfgs in
  let to_scfg_t t =
    let (dfast, tok) = t.dfastate in
    let nfacfgs = t.nfacfgs in
    let (fresh_state, dfast', nfacfgs') = S.extend_dfa dfa dfast (tok, nfacfgs) in
    if fresh_state then Some (SCFG.mk dfast' nfacfgs')
    else None in
  (List.filter_map to_scfg_t ambig, List.filter_map to_scfg_t ok)
}
;

(** extend_branches:

  (1) all SCFG.t in [l] are ambiguous
  (2) all have different [SCFG.dfastate]
  (3) use extend_branches1 to extend them, producing (list SCFG.t) * (list SCFG.t)
  (4) concat all the ambig, all the ok
 *)
type branches_toks_list = list SCFG.t ;
value extend_branches loc (cg_memo : cg_memo_t) dfa (l : list SCFG.t) : (list SCFG.t * list SCFG.t) = do {
  let open SCFG in
  let open NFACFG in

  assert (List.for_all (ambiguous_scfg dfa) l) ;
  assert (Std.distinct (List.map SCFG.dfastate l) || List.for_all (S.is_initial dfa) (List.map SCFG.dfastate l)) ;
  let ambig_ok_l =
    l
    |> List.map (extend_branches1 loc cg_memo dfa) in
  (ambig_ok_l |> List.map fst |> List.concat,
   ambig_ok_l |> List.map snd |> List.concat)
}
;

value rec compute_firstk_depth loc ((cg, _) as cg_memo) dfa ename ~{depth} (ambig_l, ok_l) : list SCFG.t = do {
  Fmt.(pf stderr "%s.compute_firstk_depth(%s, %d) (ambiguous=%d, ok=%d) paths\n%!"
         S.prefix
         (Name.print ename) depth (List.length ambig_l) (List.length ok_l)) ;
  if depth = 0 then
    raise_failwithf (CG.adjust_loc cg loc) "compute_firstk_depth(%s): exceeded depth and still ambiguous" (Name.print ename)
  else
    let (ambig_l', ok_l') = extend_branches loc cg_memo dfa ambig_l in
    if ambig_l'=[] then ok_l' @ ok_l
    else compute_firstk_depth loc cg_memo dfa ename ~{depth=depth-1} (ambig_l', ok_l' @ ok_l)
}
;

value _compute_firstk ~{depth} ((cg, _) as cg_memo) e = do {
  let loc = e.ae_loc in
  let open SCFG in
  let atn = CG.gram_atn cg in
  let nfacfgs =
    (List.hd e.ae_levels).al_rules.au_rules
    |> List.mapi (fun i r ->
           let node = Raw.entry_branch atn e.ae_name i in
           let pri = match r.ar_psymbols with [
             [{ap_symb=ASpriority _ n} :: _] -> n
           | _ -> 0
           ] in
           NFACFG.{branchnum=i; priority=pri; cfgs=[{CFG.state=node; stack=[]; mutated=False}]}) in
  let dfa = S.mk_dfa nfacfgs in
  let scfg = SCFG.mk (S.initial dfa) nfacfgs in
  let scfg = scfg_closure loc cg_memo scfg in
  let l =
    if not (ambiguous_scfg dfa scfg) then
      [scfg]
    else
      compute_firstk_depth e.ae_loc cg_memo dfa e.ae_name ~{depth=depth} ([scfg], []) in
  assert (not (List.exists (ambiguous_scfg dfa) l)) ;
  let l = l
  |> List.map (fun (t : SCFG.t) ->
         let p0 = match t.SCFG.nfacfgs with [
             [p0] -> p0
           | [] ->
              Fmt.(raise_failwithf (CG.adjust_loc cg e.ae_loc) "%s.compute_firstk(%s): no NFACFGs in SCFG:\n%a"
                     S.prefix (Name.print e.ae_name)
                     SCFG.pp t
              )

           | l ->
             List.hd (l |> List.stable_sort (fun p1 p2 -> -(Int.compare p1.NFACFG.priority p2.NFACFG.priority)))
           ] in
         (p0.NFACFG.branchnum, t.SCFG.dfastate)
       )
  |> Std.nway_partition (fun (n1,_) (n2,_) -> n1=n2)
  |> List.map (fun l ->
      let n = fst (List.hd l) in
      (n, List.map snd l)) in
  (l, dfa)
}
;


value compute_firsts ((cg, _) as cg_memo) e = do {
  let loc = e.ae_loc in
  let open SCFG in
  let atn = CG.gram_atn cg in
  let nfacfgs =
    (List.hd e.ae_levels).al_rules.au_rules
    |> List.mapi (fun i r ->
           let node = Raw.entry_branch atn e.ae_name i in
           let pri = match r.ar_psymbols with [
             [{ap_symb=ASpriority _ n} :: _] -> n
           | _ -> -1
           ] in
           NFACFG.{branchnum=i; priority=pri; cfgs=[{CFG.state=node; stack=[]; mutated=False}]}) in
  let dfa = S.mk_dfa nfacfgs in
  let scfg = SCFG.mk (S.initial dfa) nfacfgs in
  let scfg = scfg_closure loc cg_memo scfg in
  let next_l : list (Step.t * NFACFG.t) = scfg.SCFG.nfacfgs |> List.concat_map (extend1 loc cg_memo) in
  List.map fst next_l
}
;


value duration stime etime =
  Int64.of_float (1000.0 *. 1000.0 *. 1000.0 *. (etime -. stime))
;

value compute_firstk ~{depth} cg e = do {
  let loc = e.ae_loc in
  let stime = Unix.gettimeofday() in
  let rv = _compute_firstk ~{depth} cg e in
  let etime = Unix.gettimeofday() in
  if etime -. stime > 1.0 then
    let dur = duration stime etime in
    Fmt.(pf stderr "ELAPSED %s.compute_firstk(%s): %a\n%!"
           S.prefix (Name.print e.ae_name)
           uint64_ns_span dur
    )
  else () ;
  rv
}
;
end ;

module GraphDFAState = struct
  module Node = struct
    type t = (int * list Step.t) [@@deriving (show,eq,ord) ;];
    value print (n,toks) = Fmt.(str "%d [%a]" n (list ~{sep=const string " "} Step.pp) toks) ;
    value pp_hum pps n = Fmt.(pf pps "%s" (print n)) ;
  end ;
  module Label = struct
    type t = Step.t [@@deriving (show,eq,ord) ;] ;
    value print = Step.print ;
    value pp_hum pps x = Fmt.(pf pps "%s" (print x)) ;
  end ;
  module G = Graph(Node)(Label) ;
  type t = {
      g : G.t
    ; nodectr : Ctr.t
    ; cfg2node : MHBIJ.t (list NFACFG.t) Node.t
    ; initial : Node.t
    } ;
  value mk_dfa init_nfacfgs =
    let g = G.mk() in
    let nodectr = Ctr.mk() in
    let cfg2node = MHBIJ.mk (23, 23) in
    let initial = (Ctr.next nodectr, []) in
    let initial = G.add_node g initial in
    let _ = MHBIJ.add cfg2node (NFACFG.canon_list init_nfacfgs, initial) in
    {
      g = g
    ; nodectr = nodectr
    ; cfg2node = cfg2node
    ; initial = initial
    } ;
  type state_t = Node.t [@@deriving (show,eq,ord) ;] ;
  value initial dfa = dfa.initial ;
  value is_initial dfa x = x = dfa.initial ;

  value associate_nfacfgs_to_state dfa nfacfgs st =
    MHBIJ.add dfa.cfg2node (nfacfgs, st)
  ;
  value state_to_nfacfgs dfa st =
    match MHBIJ.inv dfa.cfg2node st with [
          [x] -> x
        | _ -> assert False
        ]
  ;
  value add_edge dfa (st, t, st') =
    G.add_edge  dfa.g (st, t, st') ;
  value extend_dfa dfa ((_, sttoks) as st) (t,nfacfgs) =
    let nfacfgs = NFACFG.canon_list nfacfgs in
    match MHBIJ.map dfa.cfg2node nfacfgs with [
        st' -> do {
          add_edge dfa (st, t, st') ;
          (False, st', nfacfgs)
        }
      | exception Not_found ->
         let st' = (Ctr.next dfa.nodectr, sttoks@[t]) in
         let st' = G.add_node dfa.g st' in
         let _ = associate_nfacfgs_to_state dfa nfacfgs st' in
         let _ = add_edge dfa (st, t, st') in
         (True, st', nfacfgs)
      ] ;
  value prefix = "graph";
end ;
module GraphDFA = BuildDFA(GraphDFAState) ;

module GraphFirstk = struct
open GraphDFA ;
open GraphDFAState ;

value export_dfa dfa =
  let open EDFA in
  let nodes = List.stable_sort Stdlib.compare (G.nodes dfa.g) in
  let initial = fst dfa.initial in
  let convert_state ((n, _) as st) =
    let nfacfgs = state_to_nfacfgs dfa st in
    let edges = G.edges dfa.g st in
    let trans = List.map (fun (_, tok, (d, _)) -> (tok, d)) edges in
    let trans = List.stable_sort Stdlib.compare trans in
    let final =
      if trans <> [] then [] else
      nfacfgs
      |> List.stable_sort (fun p1 p2 -> -(Int.compare p1.NFACFG.priority p2.NFACFG.priority))
      |> List.map (fun p -> p.NFACFG.branchnum) in

    {num=n; final=final; transitions=trans} in
  {init=initial; states=List.map convert_state nodes}
;

value compute_dfa cg_memo e =
  match compute_firstk ~{depth=4} cg_memo e with [
      (_, dfa) -> Some (export_dfa dfa)
    | exception exn ->
       let bts = Printexc.(get_raw_backtrace() |> raw_backtrace_to_string) in       
       let msg = Printexc.to_string exn in do {
        Fmt.(pf stderr "%s\n%s\n%!" msg bts) ;
        None
      }
    ]
;

value store_dfa ((cg, _) as cg_memo) e =
  let dfa_opt = compute_dfa cg_memo e in
  CG.set_atn_dfa cg e.ae_name dfa_opt
;

value dfa_to_firsts cg e dfa =
  let {EDFA.init=initial; states=states} = dfa in
  match states |> List.find_opt (fun {EDFA.num=st} -> st = initial) with [
      Some {EDFA.transitions=trans} -> List.map fst trans
    | None -> Fmt.(failwithf "store_first(%a): internal error: DFA did not have an initial state"
                     Name.pp e.ae_name)
    ]
;

value store_first ((cg, _) as cg_memo) e =
  match compute_firsts cg_memo e with [
      l ->
      CG.set_atn_first cg e.ae_name l
    | exception (Ploc.Exc _ _)
    | exception (Failure _) -> ()
    ]
;



end ;

end ;

module BuildATN = struct

value exec cg = do {
  ATN.Build.grammar (CG.gram_atn cg) cg ;
  cg
}
;
end ;

module ATNFirstFollow = struct
open ATN.GraphFirstk ;

value exec cg = do {
(*
    (CG.gram_entries cg)
    |> List.iter (store_firstk cg) ;
 *)
    let memo = ATN.GraphDFA.Memo.mk() in
    let cg_memo = (cg, memo) in
    (CG.gram_entries cg)
    |> List.iter (ATN.GraphFirstk.store_dfa cg_memo) ;
    (CG.gram_entries cg)
    |> List.iter (store_first cg_memo) ;
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
open Token ;


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

    | ASoptv loc g e0 s -> do {
        let s_body = compile1_symbol cg loc e s in
        <:expr< parse_optv $e0$ $s_body$ >>
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
    | ASoptv loc _ e0 s -> do {
        let s_body = compile1_symbol cg loc e s in
        (SpNtr loc patt (must <:expr< parse_optv $e0$ $s_body$ >>), SpoNoth)
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

    | ASsyntactic loc s ->
       let exp = <:expr< (fun strm -> if $compile_predicate cg e s$ then
                                        () else raise Stream.Failure) >> in
       (SpNtr loc patt (must exp), SpoNoth)

    | ASsemantic loc e ->
       let exp = <:expr< (fun strm -> if $e$ then
                                        () else raise Stream.Failure) >> in
       (SpNtr loc patt (must exp), SpoNoth)

    | s -> do {
        CG.add_failuref cg (CG.adjust_loc cg (loc_of_a_symbol s)) e.ae_name "compile1_psymbol: %s" Pr.(symbol~{pctxt=errmsg} Pprintf.empty_pc s) ;
        failwith "caught"
      }
    ]

and compile_predicate cg e s =
  match s with [
      ASsyntactic loc s ->
      let spred_expr = compile1_symbol cg loc e s in
      <:expr<
        try do { ignore ($spred_expr$ (clone_stream strm)) ; True }
               with [ (Stream.Failure | Stream.Error _) -> False ]
                    >>
    | ASsemantic loc e -> e
    ]
;

value compile1_psymbols cg loc e psl =
  let rec crec must lefts = fun [
        [({ap_symb=ASpriority _ _} as ps) :: t] -> crec must (lefts@[ps]) t
      | [({ap_symb=ASmutation_barrier _} as ps) :: t] -> crec must (lefts@[ps]) t
      | [] -> []
      | [h ::t] -> [compile1_psymbol cg loc e must lefts h :: crec True (lefts@[h]) t]
      ] in crec False e.ae_preceding_psymbols psl
;

value rule_to_exparser cg e r =
  let loc = r.ar_loc in
  let r = match r with [
        {ar_action = None ; ar_psymbols=[{ap_patt=None; ap_symb=ASkeyw _ kw}]} ->
        { (r) with ar_action = Some <:expr< $str:kw$ >> }
      | r -> r ] in
  let spc_list = compile1_psymbols cg loc e r.ar_psymbols in
  let action = match r.ar_action with [ None -> <:expr< () >> | Some a -> a ] in
  let freelids = FreeLids.free_lids_of_expr action in
  let (has_loc, action) =
  if List.mem "loc" freelids then
    (True, <:expr< let loc = Grammar.loc_of_token_interval bp ep in $action$ >>)
  else (False, action) in
  (has_loc, (spc_list, if has_loc then Some <:patt< ep >> else None, action))
;

value compile1_rule cg e r =
  let loc = r.ar_loc in
  let (has_loc, branch) = rule_to_exparser cg e r in
  let p = (if has_loc then Some <:patt< bp >> else None, [branch]) in
  cparser loc p
;

value compile1_rules cg e rl = do {
  assert (rl <> []) ;
  let loc = (List.hd rl).ar_loc in
  let l = List.map (rule_to_exparser cg e) rl in
  let has_loc = List.exists fst l in
  let branches = List.map snd l in
  let p = (if has_loc then Some <:patt< bp >> else None, branches) in
  cparser loc p
}
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
  let branch_body = <:expr< $lid:(statename newst)$ (ofs+1) >> in
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
  let branch_body = <:expr< $lid:(statename newst)$ (ofs+1) >> in
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
  let branch_body = <:expr< $lid:(statename newst)$ (ofs+1) >> in
  match cls with [
    CLS s None ->
    let patt = <:patt< Some ($str:s$, _) >> in
    (patt, <:vala< None >>, branch_body)

  | CLS s (Some tok) ->
    let patt = <:patt< Some ($str:s$, $str:String.escaped tok$) >> in
    (patt, <:vala< None >>, branch_body)

  | SPCL s ->
    let patt = <:patt< Some ("", $str:s$) >> in
    (patt, <:vala< None >>, branch_body)

  | ANTI _ -> assert False
  ]
;

value edges_to_branches loc states edges =
  let open EDFA in
  let find_state num =
    try
      List.find (fun st -> num = st.num) states
    with Not_found -> failwithf "edges_to_branches internal error: state %d not found" num in
  let state_is_final num =
    let st = find_state num in
    [] <> st.final in

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

value convert_exported_dfa (init, initre, states) : EDFA.t =
  let conv_edge (t, st) = (Step.TOKEN_STEP t, st) in
  let conv_state (i, rex, final, trans) =
    let final = match final with [
          Some (OUTPUT n) -> [n]
        | None -> []
        | _ -> assert False ] in
    {EDFA.num=i; final=final; transitions=List.map conv_edge trans} in
  {EDFA.init=init; states=List.map conv_state states}
;

value dfa_states_past_start dfa =
  let open EDFA in
  let past_start = MHS.mk 23 in
  let pass1 () =
    dfa.states
    |> List.iter (fun st ->
           st.transitions |> List.iter (fun [
               (Step.TOKEN_STEP _, st') -> MHS.add st' past_start
             | (_, st') when MHS.mem st.num past_start -> MHS.add st' past_start
             | _ -> ()
             ])) in
  let rec fix () = do {
    let oldv = MHS.toList past_start |> List.stable_sort Int.compare in
    pass1 () ;
    let newv = MHS.toList past_start |> List.stable_sort Int.compare in
    if oldv = newv then ()
    else fix ()
  } in do {
    fix() ;
    MHS.toList past_start
  }
;

value check_dfa_implementable cg e dfa =
  let open EDFA in
  let states_past_start = dfa_states_past_start dfa in
  let state_preds_list =
    dfa.states
    |> List.filter_map (fun st ->
           let preds = st.transitions |> List.filter_map (fun [ (Step.PRED_STEP s, _) -> Some s | _ -> None ]) in
           if preds = [] then None
           else Some (st.num, preds)
         ) in
  if [] <> Std.intersect (List.map fst state_preds_list) states_past_start then
    let pp_symbol pps s = Fmt.(pf pps "%s" Pr.(symbol ~{pctxt=errmsg} Pprintf.empty_pc s)) in
    Fmt.(raise_failwithf (CG.adjust_loc cg e.ae_loc)
           "check_dfa_implementable: DFA for entry %a has non-start-states with outgoing syntactic predicates (and we're not yet hoisting predicates leftward):\n%a"
           Name.pp e.ae_name
           (list ~{sep=const string "\n"} (pair ~{sep=const string ": "} int (list ~{sep=const string " "} pp_symbol)))
           state_preds_list)
  else ()
;

value letrec_nest cg e dfa = do {
  let ctr = Ctr.mk ~{initv=1} () in
  let extra_branches = ref [] in
  let open EDFA in
  check_dfa_implementable cg e dfa ;
  let states_past_start = dfa_states_past_start dfa in
  let states = List.stable_sort Stdlib.compare dfa.states in
  let open Token in
  let loc = Ploc.dummy in
  let find_state st =
    try
      List.find (fun {EDFA.num=i} -> st = i) states
    with Not_found -> failwithf "letrec_nest internal error: state %d not found" st in
  let state_is_final st =
    let st = find_state st in
    [] <> st.EDFA.final in
  let export_state st =
    match st.final with [
        [] ->
        let (pred_edges, token_edges) =
          st.transitions |> Ppxutil.filter_split (fun [ (Step.PRED_STEP _, _) -> True | _ -> False ]) in
        let match_tree =
          let edges = token_edges |> List.map (fun [ (Step.TOKEN_STEP t, s) -> (t,s) ]) in
          let edges = List.stable_sort Stdlib.compare edges in
          if edges = [] then <:expr< None >> else
            let branches = edges_to_branches loc dfa.states edges in
            let branches = branches @ [
                  (<:patt< _ >>, <:vala< None >>, <:expr< None >>)
                ] in
            <:expr< match must_peek_nth (ofs+1) strm with [
                        $list:branches$
                      ] >> in do {
          if [] <> pred_edges then assert (not (List.mem st.num states_past_start)) else () ;
          let pred_edges = pred_edges |> List.map (fun [ (Step.PRED_STEP s, st) -> (s,st) ]) in
          let pred_edges = List.stable_sort Stdlib.compare pred_edges in
          let rhs = List.fold_right (fun (s, st) rhs ->
                        <:expr< if $compile_predicate cg e s$
                                then $lid:(statename st)$ ofs
                                else $rhs$ >>)
                      pred_edges match_tree in
          (<:patt< $lid:(statename st.num)$ >>, <:expr< fun ofs -> $rhs$ >>, <:vala< [] >>)
        }
        | [output] ->
           (<:patt< $lid:(statename st.num)$ >>, <:expr< fun ofs -> Some (ofs, $int:string_of_int output$) >>, <:vala< [] >>)
        | l ->
           let output = -(Ctr.next ctr) in do {
            Std.push extra_branches (output, l) ;
            (<:patt< $lid:(statename st.num)$ >>, <:expr< fun ofs -> Some (ofs, $int:string_of_int output$) >>, <:vala< [] >>)
        }
      | _ -> assert False
      ]
  in
  let bindl = List.map export_state dfa.states in
  let e =
    <:expr< fun strm ->
            let open Llk_regexps in
            let open Token in
            let rec $list:bindl$ in $lid:(statename dfa.init)$ 0 >> in
  (e, extra_branches.val)
}
;

value compile1b_branch cg ename branchnum rl = do {
  assert ([] <> rl) ;
  let loc = (List.hd rl).ar_loc in
  let body = compile1_rules cg ename rl in
  (<:patt< Some (_, $int:string_of_int branchnum$ ) >>, <:vala< None >>, body)
}
;

value compute_predictor cg e =
  match CG.atn_dfa cg e.ae_name with [
      Some dfa -> (letrec_nest cg e dfa, "<text not available>")
    | None -> Fmt.(raise_failwithf (CG.adjust_loc cg e.ae_loc) "compute_predictor: no DFA for prediction of entry %a" Name.pp e.ae_name) 
    ]
;

value compile1b_entry cg e =
  let loc = e.ae_loc in
  let ename = e.ae_name in
  let rl = (List.hd e.ae_levels).al_rules.au_rules in
  if rl = [] then
    let rhs = <:expr< fun __strm__ -> raise Stream.Failure >> in
    [(<:patt< $lid:Name.print ename$ >>, rhs, <:vala< [] >>)]
  else
  let ((predictor, extra_branches), retxt) = compute_predictor cg e in
  let predictor_name = (Name.print ename)^"_regexp" in
   let branches = rl |> List.mapi (fun i r -> (i, [r])) in
   let extra_branches =
     extra_branches
     |> List.map (fun (i, l) -> (i, l |> List.map (List.nth rl))) in
   let branches = 
    (branches@extra_branches) |> List.map (fun (i, rl) -> compile1b_branch cg e i rl) in
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

value compile_entry cg e = compile1b_entry cg e ;

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
      Dump.report_compilation_errors cg
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
    |> List.sort_uniq Token.compare
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
  |> S7LiftListsFully.exec
  |> Dump.exec "After S7LiftListsFully"
;

value expand_lists loc ?{bootstrap=False} s =
  s
  |> lambda_lift loc ~{bootstrap=bootstrap}
  |> S7ExpandListsPartially.exec
  |> Dump.exec "After S7ExpandListsPartially"
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

value expand_flag_vala loc ?{bootstrap=False} s =
  s
  |> lift_left_assoc loc ~{bootstrap=bootstrap}
  |> S9ExpandFlagVala.exec
  |> Dump.exec "After S9ExpandFlagVala"
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

value unit_entry_elim loc ?{bootstrap=False} s =
  s
  |> lambda_lift2 loc ~{bootstrap=bootstrap}
  |> S10UnitEntryElim.exec
;

value atn loc ?{bootstrap=False} s =
  s
  |> unit_entry_elim loc ~{bootstrap=bootstrap}
  |> CheckLeftRecursion.exec
  |> SortEntries.exec
  |> BuildATN.exec
  |> Dump.exec "grammar before firstk"
;

value firstk loc ?{bootstrap=False} s =
  s
  |> atn loc ~{bootstrap=bootstrap}
  |> ATNFirstFollow.exec
;
(*
value entry_regexps loc ?{bootstrap=False} s =
  s
  |> firstk loc ~{bootstrap=bootstrap}
  |> EntryRegexps.exec
;
 *)
value codegen loc ?{bootstrap=False} s =
  s
  |> firstk loc ~{bootstrap=bootstrap}
  |> Dump.exec "final grammar before codegen"
  |> Codegen.exec
;

end ;

Pcaml.add_option "-llk-report-verbose"
  (Arg.Unit (fun _ ??? Dump.report_verbose.val := True))
  "Enable verbose reporting from the LLK parser-generator.";
