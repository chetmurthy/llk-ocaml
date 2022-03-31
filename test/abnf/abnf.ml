(* camlp5r *)
(* abnf.ml,v *)

value input_file = ref "" ;
value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;

value lexer = Plexing.lexer_func_of_ocamllex_located Abnflexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

type binop = [ ADD | SUB | DIV | MUL ] ;
type unop = [ PLUS | MINUS ] ;
type expr = [
  BINOP of Ploc.t and binop and expr and expr
| UNOP of Ploc.t and unop and expr
| INT of Ploc.t and int
| VAR of Ploc.t and string ]
and stmt = [
  ASSIGN of Ploc.t and string and expr
| EXPR of Ploc.t and expr
]
;

value loc_of_expr = fun [
  BINOP loc _ _ _ -> loc
| UNOP loc _ _ -> loc
| INT loc _ -> loc
| VAR loc _ -> loc
]
;
value loc_of_stmt = fun [
  ASSIGN loc _ _ -> loc
| EXPR loc _ -> loc
]
;

value g = Grammar.gcreate lexer;

value loc_strip_comment loc = Ploc.with_comment loc "" ;

type element = [
    ID of string
  | GROUP of alternation
  | OPTION of alternation
  | STRING of string
  | NUMBER of string
  | PROSE of string
  ]
and repeat_ = (option string * option string)
and repetition = (option repeat_ * element)
and concatenation = [ CONC of list repetition ]
and alternation = [ ALT of list concatenation ]
and rule_ = (string * bool * alternation)
and rulelist = list rule_
;

[@@@llk
{foo|
GRAMMAR Abnf:
  EXTEND g ;
  EXPORT: rulelist ;
  rulelist: [ [ l = LIST0 rule_ ; EOI -> l ] ] ;
  rule_: [ [ id = ID ; "=" ; f = FLAG "/" ; l = elements -> (id, f, l) ] ] ;
  elements: [ [ a = alternation -> a ] ] ;
  alternation: [ [ l = LIST1 concatenation SEP "/" -> ALT l ] ] ;

concatenation:
  [ [ x = repetition; y = concatenation2 → CONC [x :: y] ] ]
;
concatenation2:
  [ [ x__0004 = repetition; y__0004 = concatenation2 → [x__0004 :: y__0004]
    | → [] ] ]
;

  repetition: [ [ r = OPT repeat_ ; e = element -> (r,e) ] ] ;
  repeat_: [ [ n = INT -> (Some n, Some n) | ([ OPT INT ; "*" ])? ; n = OPT INT ; "*" ; m = OPT INT -> (n,m) ] ] ;
  element: [ [
    id = ID -> ID id
  | g = group -> GROUP g
  | o = option -> OPTION o
  | s = STRING -> STRING s
  | n = NUMBERVALUE -> NUMBER n
  | p = PROSEVALUE -> PROSE p
  ] ] ;
  group: [ [ "(" ; a = alternation ; ")" -> a ] ] ;
  option: [ [ "[" ; a = alternation ; "]" -> a ] ] ;
END;
|foo};
] ;

value parse_rulelist = Grammar.Entry.parse Abnf.rulelist ;


module Pr = struct
open Pretty ;
open Prtools ;

value pair_with s l = List.map (fun g -> (g, s)) l ;


value opt f pc x = match x with [ None -> pprintf pc "" | Some x -> pprintf pc "%p" f x ] ;

value rec rulelist pc rl =
  pprintf pc "@[<b>%p@]@ " (vlist rule) rl

and rule pc (id, b, e) =
  pprintf pc "%s = %s%p@;" id (if b then "/ " else "") alternation e

and alternation pc = fun [
      ALT l ->
      pprintf pc "%p" (plist concatenation 0) (pair_with "/ " l)
    ]

and concatenation pc = fun [
      CONC l ->
      pprintf pc "%p" (plist repetition 0) (pair_with " " l)
    ]

and repetition pc (r, e) = pprintf pc "%p%p" repeat_opt r element e

and repeat_opt pc x = opt repeat_ pc x

and repeat_ pc (nopt, mopt) =
  pprintf pc "%p*%p" int_opt nopt int_opt mopt

and int_opt pc x = opt (fun pc n -> pprintf pc "%s" n) pc x

and element pc = fun [
      ID s -> pprintf pc "%s" s
    | GROUP a -> pprintf pc "(%p)" alternation a
    | OPTION a -> pprintf pc "[%p]" alternation a
    | STRING s -> pprintf pc "\"%s\"" s
    | NUMBER n -> pprintf pc "%s" n
    | PROSE s -> pprintf pc "%s" s
    ]
;
end ;

open Printf;

Pretty.line_length.val := 100 ;

if not Sys.interactive.val then
try
    let l = parse_rulelist (Stream.of_channel stdin) in do {
      printf "%s" (Pr.rulelist Pprintf.empty_pc l)
    }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
