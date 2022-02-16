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

value equal_expr = Reloc.eq_expr ;
value equal_patt = Reloc.eq_patt ;

value split_ext = ref False;

type loc = Ploc.t [@@deriving (show) ;];
value equal_loc a b = True ;
value compare_loc a b = 0 ;

type regexp = Llk_regexps.PSyn.t ;
value compare_regexp = Llk_regexps.PSyn.R.compare ;
value equal_regexp = Llk_regexps.PSyn.R.equal ;
value pp_regexp pps re = Fmt.(pf pps "%s" (Llk_regexps.PSyn.print re)) ;

type astre = Llk_regexps.astre [@@deriving (show,eq,ord) ;] ;

type a_position = [
    POS_LEVEL of string
  | POS_LIKE of string
  | POS_AFTER of string
  | POS_BEFORE of string
  | POS_FIRST | POS_LAST
]
and a_assoc = [
    LEFTA
  | RIGHTA
  | NONA
]
and a_entry =
  { ae_loc : loc;
    ae_name : string;
    ae_pos : option a_position;
    ae_formals : list patt ;
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
  | ASnext of loc and list expr
  | ASnterm of loc and string and list expr and option string
  | ASregexp of loc and string
  | ASopt of loc and a_symbol
  | ASleft_assoc of loc and a_symbol and a_symbol and expr
  | ASrules of loc and a_rules
  | ASself of loc and list expr
  | AStok of loc and string and option string
  | ASvala of loc and a_symbol and list string
  ]
and lmin_len =
  [ LML_0 | LML_1 ]
and _top = {
    gram_loc: loc
  ; gram_id: string
  ; gram_globals: list string
  ; gram_regexp_asts: list (string * astre)
  ; gram_regexps: list (string * regexp)
  ; gram_entries : list a_entry
  } [@@deriving (show,eq,ord) ;] ;

type top = _top ;
value norm_top g = {(g) with gram_globals = List.sort String.compare g.gram_globals
                           ; gram_entries = List.sort compare_a_entry g.gram_entries } ;
value show_top = show__top ;
value eq_top x y = equal__top (x |> norm_top) (y |> norm_top) ;
value compare_top x y = compare__top (x |> norm_top) (y |> norm_top) ;
