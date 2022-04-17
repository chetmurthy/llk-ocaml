(* camlp5r *)
(* cminus.ml,v *)

open Pa_ppx_base ;
open Pp_MLast ;
open Ord_MLast ;
open Pa_ppx_testutils ;
open Papr_util ;
open Pa_ppx_utils ;
open Primtypes ;
open Llk_types ;
open Print_gram ;

value lexer = Plexing.lexer_func_of_ocamllex_located Cminuslexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;

value loc_strip_comment loc = Ploc.with_comment loc "" ;

[@@@llk
{foo|
(*
keywords: "char"; "for"; "int"
specials: "(" | ")" | "+" | "," | ";" | 
"<" | "=" | "==" | "{" | "}"
*)
GRAMMAR CMinus:
  EXTEND g ;
    EXPORT: program_eoi program declaration variable declarator function_ formalParameter type_ block stat
      forStat assignStat expr condExpr aexpr atom;
    
    program_eoi: [ [ program ; EOI ] ] ;
    
    program:
      
      [ [ GREEDY LIST1 declaration ] ]
    ;
    declaration:
      
      [ [ variable
        | function_ ] ]
    ;
    variable:
      
      [ [ type_; declarator; ";" ] ]
    ;
    declarator:
      
      [ [ ID ] ]
    ;
    function_:
      
      [ [ type_; ID; "("; GREEDY OPT [ formalParameter; GREEDY LIST0 [ ","; formalParameter ] ]; ")"; block ] ]
    ;
    formalParameter:
      
      [ [ type_; declarator ] ]
    ;
    type_:
      
      [ [ "int" -> ()
        | "char" -> ()
        | ID ] ]
    ;
    block:
      
      [ [ "{"; NONGREEDY LIST0 variable; GREEDY LIST0 stat; "}" ] ]
    ;
    stat:
      
      [ [ forStat
        | expr; ";"
        | block
        | assignStat; ";"
        | ";" -> () ] ]
    ;
    forStat:
      
      [ [ "for"; "("; assignStat; ";"; expr; ";"; assignStat; ")"; block ] ]
    ;
    assignStat:
      
      [ [ ID; "="; expr ] ]
    ;
    expr:
      
      [ [ condExpr ] ]
    ;
    condExpr:
      
      [ [ aexpr; GREEDY OPT [ [ "=="; expr | "<"; aexpr ] ] ] ]
    ;
    aexpr:
      
      [ [ atom; GREEDY LIST0 [ "+"; atom ] ] ]
    ;
    atom:
      
      [ [ ID
        | INT
        | "("; expr; ")" ] ]
    ;
END;
|foo};
] ;

value parse_program_eoi = Grammar.Entry.parse CMinus.program_eoi ;


if not Sys.interactive.val then
try
  let (ic, ifname) = match Sys.argv.(1) with [
      x -> (open_in x, x)
    | exception (Invalid_argument _) -> (stdin, "<stdin>")
  ] in do {
    Cminuslexer.input_file.val := ifname ;
    let g = parse_program_eoi (Stream.of_channel ic) in
    print_string "OK\n"
  }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
