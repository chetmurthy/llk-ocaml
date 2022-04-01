(* camlp5r *)
(* abb.ml,v *)

value input_file = ref "" ;
value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;

value lexer = Plexing.lexer_func_of_ocamllex_located Abblexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;

value loc_strip_comment loc = Ploc.with_comment loc "" ;

[@@@llk
{foo|
GRAMMAR Abb:
  EXTEND g ;
  EXPORT: module_ ;

(*
module
    : moduleData EOF
    ;
*)
  module_: [ [ moduledata ; EOI ] ] ;

(*
moduleData
    : MODULE moduleName NEWLINE
      dataList
      NEWLINE*
      ENDMODULE
    ;
*)
  moduledata: [ [
      "module"; moduleName; NEWLINE;
      dataList; LIST0 NEWLINE; "endmodule"
    ] ] ;

(*      
moduleName
    : IDENTIFIER
    | procCall
    ;
*)
  moduleName: [ [ (* IDENTIFIER | *)procCall ] ] ;

(*
dataList
    : (NEWLINE
    | declaration NEWLINE
    | procedure NEWLINE)*
    ;
*)
  dataList: [ [ LIST0 [ NEWLINE | [declaration ; NEWLINE] | [ procedure ; NEWLINE ] ] ] ] ; 

(*
procedure
    : PROC procCall NEWLINE
      (functionCall NEWLINE)*
    ENDPROC
    ;
*)
  procedure: [ [ "proc"; procCall; NEWLINE; LIST0 [ functionCall ; NEWLINE ] ; "endproc" ] ] ;

(*
procCall
    : procName procParameter?
    ;
*)

  procCall: [ [ procName; OPT procParameter ] ] ;

(*
procName
    : IDENTIFIER
    ;
*)
  procName: [ [ IDENTIFIER ] ] ;

(*
procParameter
    : BRACKET_OPEN IDENTIFIER? BRACKET_CLOSE
    ;
*)
  procParameter: [ [ "(";  OPT IDENTIFIER ; ")" ] ] ;

(*
functionCall
    : IDENTIFIER (functionParameter COMMA)* functionParameter SEMICOLON
    ;
*)
  functionCall: [ [ IDENTIFIER;  LIST1 functionParameter SEP "," ;  ";" ] ] ;

(*
functionParameter
    : ON_CALL
    | OFF_CALL
    | primitive
    | IDENTIFIER
    ;
*)
  functionParameter:
  [ [ ON_CALL
    | OFF_CALL
    | primitive
    | IDENTIFIER
    ] ] ;

(*
declaration
    : init_ type_ IDENTIFIER (EQUALS expression)? SEMICOLON
    ;
*)

  declaration: [ [ init_; type_; IDENTIFIER; OPT [ ":="; expression ] ; ";" ] ] ;

(*
type_
    : ( TOOLDATA | WOBJDATA | SPEEDDATA | ZONEDATA | CLOCK | BOOL )
    ;
*)
  type_: [ [ "tooldata" | "wobjdata" | "speeddata" | "zonedata" | "clock" | "bool" ] ] ;

(*
init_
    : LOCAL? ( CONST | PERS | VAR )
    ;
*)

  init_: [ [ OPT "local" ;  [ "const" | "pers" | "var" ] ] ] ;

(*
expression
    : array_ | primitive
    ;
*)
  expression: [ [ array_ | primitive ] ] ;

(*
array_
    : SQUARE_OPEN (expression COMMA)* expression SQUARE_CLOSE
    ;
*)
  array_: [ [ "["; LIST1 expression SEP ","; "]" ] ] ;

(*
primitive
    : BOOLLITERAL
    | CHARLITERAL
    | STRINGLITERAL
    | (PLUS | MINUS)? FLOATLITERAL
    | (PLUS | MINUS)? INTLITERAL
    ;
*)
  primitive:
    [ [ BOOLLITERAL
      | CHARLITERAL
      | STRINGLITERAL
      | OPT ["+" | "-"] ; FLOATLITERAL
      | OPT ["+" | "-"] ; INTLITERAL
      ] ] ;

END;
|foo};
] ;

value parse_module_ = Grammar.Entry.parse Abb.module_ ;

if not Sys.interactive.val then
try
    let l = parse_module_ (Stream.of_channel stdin) in do {
      Fmt.(pf stdout "OK\n%!")
    }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
