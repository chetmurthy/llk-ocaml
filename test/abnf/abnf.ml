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
  concatenation: [ [ l = LIST1 repetition -> CONC l ] ] ;
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
