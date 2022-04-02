(* camlp5r *)
(* abb.ml,v *)

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
  
    EXPORT: module_ moduleData moduleName dataList procedure procCall procName procParameter
      functionCall functionParameter declaration type_ init_ expression array_ primitive;
    
    
    
    module_:
      
      [ [ moduleData; EOI ] ]
    ;
    moduleData:
      
      [ [ "module"; moduleName; NEWLINE; dataList; GREEDY LIST0 NEWLINE; "endmodule" ] ]
    ;
    moduleName:
      
      [ [ procCall ] ]
    ;
    dataList:
      
      [ [ GREEDY LIST0 [ NEWLINE | declaration; NEWLINE | procedure; NEWLINE ] ] ]
    ;
    procedure:
      
      [ [ "proc"; procCall; NEWLINE; GREEDY LIST0 [ functionCall; NEWLINE ]; "endproc" ] ]
    ;
    procCall:
      
      [ [ procName; GREEDY OPT procParameter ] ]
    ;
    procName:
      
      [ [ IDENTIFIER ] ]
    ;
    procParameter:
      
      [ [ "("; GREEDY OPT IDENTIFIER; ")" ] ]
    ;
    functionCall:
      
      [ [ IDENTIFIER; GREEDY LIST1 functionParameter SEP ","; ";" ] ]
    ;
    functionParameter:
      
      [ [ ON_CALL
        | OFF_CALL
        | primitive
        | IDENTIFIER ] ]
    ;
    declaration:
      
      [ [ init_; type_; IDENTIFIER; GREEDY OPT [ ":="; expression ]; ";" ] ]
    ;
    type_:
      
      [ [ "tooldata"
        | "wobjdata"
        | "speeddata"
        | "zonedata"
        | "clock"
        | "bool" ] ]
    ;
    init_:
      
      [ [ GREEDY OPT "local"; [ "const" | "pers" | "var" ] ] ]
    ;
    expression:
      
      [ [ array_
        | primitive ] ]
    ;
    array_:
      
      [ [ "["; GREEDY LIST1 expression SEP ","; "]" ] ]
    ;
    primitive:
      
      [ [ BOOLLITERAL
        | CHARLITERAL
        | STRINGLITERAL
        | GREEDY OPT [ "+" | "-" ]; FLOATLITERAL
        | GREEDY OPT [ "+" | "-" ]; INTLITERAL ] ]
    ;
END;
|foo};
] ;

value parse_module_ = Grammar.Entry.parse Abb.module_ ;

if not Sys.interactive.val then
try
  let (ic, ifname) = match Sys.argv.(1) with [
      x -> (open_in x, x)
    | exception (Invalid_argument _) -> (stdin, "<stdin>")
  ] in do {
    Abblexer.input_file.val := ifname ;
    let l = parse_module_ (Stream.of_channel ic) in
    Fmt.(pf stdout "OK\n%!") ;
  }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
