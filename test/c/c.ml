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

value lexer = Plexing.lexer_func_of_ocamllex_located Clexer.token ;
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
keywords: "auto"; "break"; "case"; "char"; "const"; "continue"; "default"; 
"do"; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; 
"int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"; 
"struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; 
"while"
specials: "!" | "!=" | "%" | "%=" | "&" | "&&" | "&=" | "(" | 
")" | "*" | "*=" | "+" | "++" | "+=" | "," | "-" | "--" | "-=" | "->" | 
"." | "..." | "/" | "/=" | ":" | ";" | "<" | "<<" | "<<=" | "<=" | "=" | 
"==" | ">" | ">=" | ">>" | ">>=" | "?" | "[" | "]" | "^" | "^=" | "{" | 
"|" | "|=" | "||" | "}" | "~"
*)
GRAMMAR C:
  
    EXPORT: translation_unit external_declaration function_definition declaration
      declaration_specifiers init_declarator_list init_declarator storage_class_specifier
      type_specifier type_id struct_or_union_specifier struct_or_union struct_declaration_list
      struct_declaration specifier_qualifier_list struct_declarator_list struct_declarator
      enum_specifier enumerator_list enumerator type_qualifier declarator direct_declarator
      declarator_suffix pointer parameter_type_list parameter_list parameter_declaration
      identifier_list type_name abstract_declarator direct_abstract_declarator
      abstract_declarator_suffix initializer_ initializer_list argument_expression_list
      additive_expression multiplicative_expression cast_expression unary_expression
      postfix_expression unary_operator primary_expression constant expression constant_expression
      assignment_expression lvalue assignment_operator conditional_expression logical_or_expression
      logical_and_expression inclusive_or_expression exclusive_or_expression and_expression
      equality_expression relational_expression shift_expression statement labeled_statement
      compound_statement statement_list expression_statement selection_statement iteration_statement
      jump_statement;
    
    
    
    translation_unit:
      
      [ [ GREEDY LIST1 external_declaration ] ]
    ;
    external_declaration:
      
      [ [ [ ([ GREEDY OPT declaration_specifiers; declarator; GREEDY LIST0 declaration; "{" ])?;
            [ function_definition | declaration ] ] ] ]
    ;
    function_definition:
      
      [ [ GREEDY OPT declaration_specifiers; declarator;
          [ GREEDY LIST1 declaration; compound_statement | compound_statement ] ] ]
    ;
    declaration:
      
      [ [ "typedef"; GREEDY OPT declaration_specifiers; init_declarator_list; ";"
        | declaration_specifiers; GREEDY OPT init_declarator_list; ";" ] ]
    ;
    declaration_specifiers:
      
      [ [ GREEDY LIST1 [ storage_class_specifier | type_specifier | type_qualifier ] ] ]
    ;
    init_declarator_list:
      
      [ [ init_declarator; GREEDY LIST0 [ ","; init_declarator ] ] ]
    ;
    init_declarator:
      
      [ [ declarator; GREEDY OPT [ "="; initializer_ ] ] ]
    ;
    storage_class_specifier:
      
      [ [ "extern"
        | "static"
        | "auto"
        | "register" ] ]
    ;
    type_specifier:
      
      [ [ "void"
        | "char"
        | "short"
        | "int"
        | "long"
        | "float"
        | "double"
        | "signed"
        | "unsigned"
        | struct_or_union_specifier
        | enum_specifier
        | type_id ] ]
    ;
    type_id:
      
      [ [ IDENTIFIER ] ]
    ;
    struct_or_union_specifier:
      
      [ [ struct_or_union; GREEDY OPT IDENTIFIER; "{"; struct_declaration_list; "}"
        | struct_or_union; IDENTIFIER ] ]
    ;
    struct_or_union:
      
      [ [ "struct"
        | "union" ] ]
    ;
    struct_declaration_list:
      
      [ [ GREEDY LIST1 struct_declaration ] ]
    ;
    struct_declaration:
      
      [ [ specifier_qualifier_list; struct_declarator_list; ";" ] ]
    ;
    specifier_qualifier_list:
      
      [ [ GREEDY LIST1 [ type_qualifier | type_specifier ] ] ]
    ;
    struct_declarator_list:
      
      [ [ struct_declarator; GREEDY LIST0 [ ","; struct_declarator ] ] ]
    ;
    struct_declarator:
      
      [ [ declarator; GREEDY OPT [ ":"; constant_expression ]
        | ":"; constant_expression ] ]
    ;
    enum_specifier:
      
      [ [ "enum"; "{"; enumerator_list; "}"
        | "enum"; IDENTIFIER; "{"; enumerator_list; "}"
        | "enum"; IDENTIFIER ] ]
    ;
    enumerator_list:
      
      [ [ enumerator; GREEDY LIST0 [ ","; enumerator ] ] ]
    ;
    enumerator:
      
      [ [ IDENTIFIER; GREEDY OPT [ "="; constant_expression ] ] ]
    ;
    type_qualifier:
      
      [ [ "const"
        | "volatile" ] ]
    ;
    declarator:
      
      [ [ GREEDY OPT pointer; direct_declarator
        | pointer ] ]
    ;
    direct_declarator:
      
      [ [ [ IDENTIFIER | "("; declarator; ")" ]; GREEDY LIST0 declarator_suffix ] ]
    ;
    declarator_suffix:
      
      [ [ "["; constant_expression; "]"
        | "["; "]"
        | "("; parameter_type_list; ")"
        | "("; identifier_list; ")"
        | "("; ")" ] ]
    ;
    pointer:
      
      [ [ "*"; GREEDY LIST1 type_qualifier; GREEDY OPT pointer
        | "*"; pointer
        | "*" ] ]
    ;
    parameter_type_list:
      
      [ [ parameter_list; GREEDY OPT [ ","; "..." ] ] ]
    ;
    parameter_list:
      
      [ [ parameter_declaration; GREEDY LIST0 [ ","; parameter_declaration ] ] ]
    ;
    parameter_declaration:
      
      [ [ declaration_specifiers; GREEDY LIST0 [ declarator | abstract_declarator ] ] ]
    ;
    identifier_list:
      
      [ [ IDENTIFIER; GREEDY LIST0 [ ","; IDENTIFIER ] ] ]
    ;
    type_name:
      
      [ [ specifier_qualifier_list; GREEDY OPT abstract_declarator ] ]
    ;
    abstract_declarator:
      
      [ [ pointer; GREEDY OPT direct_abstract_declarator
        | direct_abstract_declarator ] ]
    ;
    direct_abstract_declarator:
      
      [ [ [ "("; abstract_declarator; ")" | abstract_declarator_suffix ];
          GREEDY LIST0 abstract_declarator_suffix ] ]
    ;
    abstract_declarator_suffix:
      
      [ [ "["; "]"
        | "["; constant_expression; "]"
        | "("; ")"
        | "("; parameter_type_list; ")" ] ]
    ;
    initializer_:
      
      [ [ assignment_expression
        | "{"; initializer_list; GREEDY OPT ","; "}" ] ]
    ;
    initializer_list:
      
      [ [ initializer_; GREEDY LIST0 [ ","; initializer_ ] ] ]
    ;
    argument_expression_list:
      
      [ [ assignment_expression; GREEDY LIST0 [ ","; assignment_expression ] ] ]
    ;
    additive_expression:
      
      [ [ multiplicative_expression;
          GREEDY LIST0 [ "+"; multiplicative_expression | "-"; multiplicative_expression ] ] ]
    ;
    multiplicative_expression:
      
      [ [ cast_expression;
          GREEDY LIST0 [ "*"; cast_expression | "/"; cast_expression | "%"; cast_expression ] ] ]
    ;
    cast_expression:
      
      [ [ "("; type_name; ")"; cast_expression
        | unary_expression ] ]
    ;
    unary_expression:
      
      [ [ postfix_expression
        | "++"; unary_expression
        | "--"; unary_expression
        | unary_operator; cast_expression
        | "sizeof"; unary_expression
        | "sizeof"; "("; type_name; ")" ] ]
    ;
    postfix_expression:
      
      [ [ primary_expression;
          GREEDY LIST0
            [ "["; expression; "]"
            | "("; ")"
            | "("; argument_expression_list; ")"
            | "."; IDENTIFIER
            | "->"; IDENTIFIER
            | "++"
            | "--" ] ] ]
    ;
    unary_operator:
      
      [ [ "&"
        | "*"
        | "+"
        | "-"
        | "~"
        | "!" ] ]
    ;
    primary_expression:
      
      [ [ IDENTIFIER
        | constant
        | "("; expression; ")" ] ]
    ;
    constant:
      
      [ [ HEX_LITERAL
        | OCTAL_LITERAL
        | DECIMAL_LITERAL
        | CHARACTER_LITERAL
        | STRING_LITERAL
        | FLOATING_POINT_LITERAL ] ]
    ;
    expression:
      
      [ [ assignment_expression; GREEDY LIST0 [ ","; assignment_expression ] ] ]
    ;
    constant_expression:
      
      [ [ conditional_expression ] ]
    ;
    assignment_expression:
      
      [ [ lvalue; assignment_operator; assignment_expression
        | conditional_expression ] ]
    ;
    lvalue:
      
      [ [ unary_expression ] ]
    ;
    assignment_operator:
      
      [ [ "="
        | "*="
        | "/="
        | "%="
        | "+="
        | "-="
        | "<<="
        | ">>="
        | "&="
        | "^="
        | "|=" ] ]
    ;
    conditional_expression:
      
      [ [ logical_or_expression; GREEDY OPT [ "?"; expression; ":"; conditional_expression ] ] ]
    ;
    logical_or_expression:
      
      [ [ logical_and_expression; GREEDY LIST0 [ "||"; logical_and_expression ] ] ]
    ;
    logical_and_expression:
      
      [ [ inclusive_or_expression; GREEDY LIST0 [ "&&"; inclusive_or_expression ] ] ]
    ;
    inclusive_or_expression:
      
      [ [ exclusive_or_expression; GREEDY LIST0 [ "|"; exclusive_or_expression ] ] ]
    ;
    exclusive_or_expression:
      
      [ [ and_expression; GREEDY LIST0 [ "^"; and_expression ] ] ]
    ;
    and_expression:
      
      [ [ equality_expression; GREEDY LIST0 [ "&"; equality_expression ] ] ]
    ;
    equality_expression:
      
      [ [ relational_expression; GREEDY LIST0 [ [ "==" | "!=" ]; relational_expression ] ] ]
    ;
    relational_expression:
      
      [ [ shift_expression; GREEDY LIST0 [ [ "<" | ">" | "<=" | ">=" ]; shift_expression ] ] ]
    ;
    shift_expression:
      
      [ [ additive_expression; GREEDY LIST0 [ [ "<<" | ">>" ]; additive_expression ] ] ]
    ;
    statement:
      
      [ [ labeled_statement
        | compound_statement
        | expression_statement
        | selection_statement
        | iteration_statement
        | jump_statement ] ]
    ;
    labeled_statement:
      
      [ [ IDENTIFIER; ":"; statement
        | "case"; constant_expression; ":"; statement
        | "default"; ":"; statement ] ]
    ;
    compound_statement:
      
      [ [ "{"; GREEDY LIST0 declaration; GREEDY OPT statement_list; "}" ] ]
    ;
    statement_list:
      
      [ [ GREEDY LIST1 statement ] ]
    ;
    expression_statement:
      
      [ [ ";"
        | expression; ";" ] ]
    ;
    selection_statement:
      
      [ [ "if"; "("; expression; ")"; statement; GREEDY OPT [ "else"; statement ]
        | "switch"; "("; expression; ")"; statement ] ]
    ;
    iteration_statement:
      
      [ [ "while"; "("; expression; ")"; statement
        | "do"; statement; "while"; "("; expression; ")"; ";"
        | "for"; "("; expression_statement; expression_statement; GREEDY OPT expression; ")";
          statement ] ]
    ;
    jump_statement:
      
      [ [ "goto"; IDENTIFIER; ";"
        | "continue"; ";"
        | "break"; ";"
        | "return"; ";"
        | "return"; expression; ";" ] ]
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
    Clexer.input_file.val := ifname ;
    let g = parse_program_eoi (Stream.of_channel ic) in
    print_string "OK\n"
  }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
