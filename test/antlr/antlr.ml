(* camlp5r *)
(* abnf.ml,v *)

open Pa_ppx_base ;
open Pp_MLast ;
open Ord_MLast ;
open Pa_ppx_testutils ;
open Papr_util ;
open Pa_ppx_utils ;
open Primtypes ;
open Llk_types ;
open Print_gram ;

value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;

value lexer = Plexing.lexer_func_of_ocamllex_located Antlrlexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;

value loc_strip_comment loc = Ploc.with_comment loc "" ;

type loc = Ploc.t [@@deriving (show,eq,ord) ;] ;

type expr = [
    EXid of loc and string
  | EXquestion of loc and expr
  | EXstar of loc and expr
  | EXplus of loc and expr
  | EXconc of loc and list expr
  | EXdisj of loc and list expr
  ] [@@deriving (show,eq,ord) ;]
;

value loc_of_expr = fun [
    EXid loc _ -> loc
  | EXquestion loc _ -> loc
  | EXstar loc _ -> loc
  | EXplus loc _ -> loc
  | EXconc loc _ -> loc
  | EXdisj loc _ -> loc
  ]
;

value mkdisj loc = fun [
  [] -> assert False
| [x] -> x
| l -> EXdisj loc l
]
;

value mkconc loc = fun [
  [] -> assert False
| [x] -> x
| l -> EXconc loc l
]
;

type rule = [
    RULEprod of loc and string and expr
  | RULEkeyword of loc and string and string
  ] [@@deriving (show,eq,ord) ;]
;
[@@@llk
{foo|
GRAMMAR ANTLR:
  EXTEND g ;
  EXPORT: grammar grammar_eoi ;

  grammar_eoi: [ [ g = grammar ; EOI -> g ] ];
  grammar: [ [
      "grammar"; id = ID ; ";" ;
      l = LIST1 rule -> (loc, id, l)
  ] ] ;

  rule: [ [
      id = ID ; ":" ; rhs = expr ; ";" -> RULEprod loc id rhs
    | id = ID ; "=" ; s = STRING ; ";" -> RULEkeyword loc id s
    ] ]
  ;

  expr:
    [
      "disj" [
        l = LIST1 NEXT SEP "|" -> mkdisj loc l
      ]
    | "conc" [
        l = LIST1 NEXT -> mkconc loc l
      ]
    | "star" LEFTA [
        e = SELF ; "*" -> EXstar loc e
      | e = SELF ; "+" -> EXplus loc e
      | e = SELF ; "?" -> EXquestion loc e
      ]
    | "simple" [
        id = ID -> EXid loc id
      | "(" ; e = expr ; ")" -> e
    ] ]
  ;

END;
|foo};
] ;

value parse_grammar_eoi = Grammar.Entry.parse ANTLR.grammar_eoi ;

module Conv = struct
  open Llk_types ;

  value keyword = fun [
    RULEkeyword _ k v ->
    let vlen = String.length v in
    let v = String.sub v 1 (vlen-2) in
    (k,v)
  ]
  ;

  value rec expr kwmap e : a_symbol =
    match e with [
        EXid loc nt ->
        (match List.assoc nt kwmap with [
             x -> ASkeyw loc x
           | exception Not_found ->
              ASnterm loc (Name.mk nt) [] None
        ])
      | EXquestion loc e ->
         ASopt loc True (expr kwmap e) 

      | EXstar loc e ->
         ASlist loc True LML_0 (expr kwmap e) None

      | EXplus loc e ->
         ASlist loc True LML_1 (expr kwmap e) None

      | EXconc loc l ->
         let sl = List.map (expr kwmap) l in
         let psl = sl |> List.map (fun s -> { ap_loc = loc; ap_patt = None ; ap_symb = s }) in
         ASrules loc { au_loc = loc ; 
                       au_rules = [{ ar_loc = loc ;
                                     ar_psymbols = psl ;
                                     ar_action = None }] }

      | EXdisj loc l ->
         let rl = List.map (expr_to_rule kwmap) l in
         ASrules loc { au_loc = loc ; 
                       au_rules = rl }
      ]

  and expr_to_rule kwmap e : a_rule =
    match e with [
        EXconc loc l ->
         let sl = List.map (expr kwmap) l in
         let psl = sl |> List.map (fun s -> { ap_loc = loc; ap_patt = None ; ap_symb = s }) in
         { ar_loc = loc ;
           ar_psymbols = psl ;
           ar_action = None }
      | e ->
         let s = expr kwmap e in
         let loc = loc_of_expr e in
         let ps = { ap_loc = loc; ap_patt = None ; ap_symb = s } in
         { ar_loc = loc ;
           ar_psymbols = [ps] ;
           ar_action = None }

      ]
  ;
  value top_expr kwmap = fun [
    EXconc loc l ->
    let sl = List.map (expr kwmap) l in
    let psl = sl |> List.map (fun s -> { ap_loc = loc; ap_patt = None ; ap_symb = s }) in
    { au_loc = loc
             ; au_rules = [{ ar_loc = loc
                           ; ar_psymbols = psl
                           ; ar_action = None
                          }]
             }

  | EXdisj _ _ as e ->
     (match expr kwmap e with [
          ASrules loc r -> r          
        ])

  | e ->
    let s = expr kwmap e in
    let loc = loc_of_expr e in
    { au_loc = loc
    ; au_rules = [{ ar_loc = loc
                  ; ar_psymbols = [{ ap_loc = loc
                                   ; ap_patt = None
                                   ; ap_symb = s
                                  }]
                  ; ar_action = None
                 }]
    }
  ]
  ;
  value entry kwmap = fun [
    RULEprod loc id rhs ->
    let rl = top_expr kwmap rhs in
    { ae_loc = loc
    ; ae_name = Name.mk id
    ; ae_pos = None
    ; ae_formals = []
    ; ae_levels = [{ al_loc = loc
                   ; al_label = None
                   ; al_assoc = None
                   ; al_rules = rl
                  }]
    ; ae_preceding_psymbols = []
    ; ae_source_symbol = None
    }
  ]
  ;

  value grammar (loc, gname, l) =
    let (prods, keywords) = Ppxutil.filter_split (fun [ RULEprod _ _ _ -> True | _ -> False ]) l in
    let kwmap = List.map keyword keywords in
    let entries = List.map (entry kwmap) prods in
    {
      gram_loc = loc
    ; gram_id = String.capitalize_ascii gname
    ; gram_extend = None
    ; gram_exports = prods |> List.map (fun [ RULEprod _ id _ -> Name.mk id ])
    ; gram_external_asts = []
    ; gram_regexp_asts = []
    ; gram_entries = entries
  }
  ;
end
;
open Printf;

Pretty.line_length.val := 100 ;

if not Sys.interactive.val then
try
  let (ic, ifname) = match Sys.argv.(1) with [
      x -> (open_in x, x)
    | exception (Invalid_argument _) -> (stdin, "<stdin>")
  ] in do {
    Antlrlexer.input_file.val := ifname ;
    let g = parse_grammar_eoi (Stream.of_channel ic) in
    let g = Conv.grammar g in
    print_string Pr.(top ~{pctxt=normal} Pprintf.empty_pc g)
  }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
