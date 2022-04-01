(* camlp5r *)
(* abnf.ml,v *)

open Pa_ppx_base ;
open Pp_MLast ;
open Ord_MLast ;

value input_file = ref "" ;
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
      l = LIST1 rule -> (id, l)
  ] ] ;

  rule: [ [
      id = ID ; ":" ; rhs = expr ; ";" -> RULEprod loc id rhs
    | "keyword" ; id = ID ; "=" ; s = STRING -> RULEkeyword loc id s
    ] ]
  ;

  expr:
    [
      "disj" [
        l = LIST1 NEXT SEP "|" -> EXdisj loc l
      ]
    | "conc" [
        l = LIST1 NEXT -> EXconc loc l
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


open Printf;

Pretty.line_length.val := 100 ;

if not Sys.interactive.val then
try
    let l = parse_grammar_eoi (Stream.of_channel stdin) in do {
      printf "OK\n%!"
    }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
