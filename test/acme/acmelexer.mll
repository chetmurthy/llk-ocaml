{

let input_file = ref "" ;;

let locate ?(comments="") lb v =
  let loc = Ploc.make_loc !input_file 1 0 (Lexing.lexeme_start lb, Lexing.lexeme_end lb) comments in
  (v, loc)

let kw_ht = Hashtbl.create 23
let _ = [] |> List.iter (fun s -> Hashtbl.add kw_ht s ())
let mixedcase_ht = Hashtbl.create 23
let _ = ([("BOOLEAN", "true");("BOOLEAN", "false")]@
          (List.map (fun s -> ("",s)) [
"abstract"; "analysis"; "and"; "any"; "attachedports"; "attachedroles"; 
"attachment"; "attachments"; "bindings"; "collect"; "component"; "components"; 
"connector"; "connectors"; "containassign"; "design"; "distinct"; "double"; 
"element"; "enum"; "exists"; "extended"; "extends"; "external";
"family"; "final"; "float"; "forall"; "group"; "groups"; "heuristic"; 
"import"; "in"; "int"; "integer"; "invariant"; "members"; "new"; "or"; 
"port"; "ports"; "power"; "private"; "properties"; "property"; "public"; 
"record"; "representation"; "representations"; "role"; "roles"; "rule"; 
"select"; "seq"; "sequence"; "set"; "string"; "style"; "system"; "to"; 
"type"; "unique"; "view"; "with"
]))
        |> List.iter (fun (ty,s) -> Hashtbl.add mixedcase_ht s ty) ;;

let kwd_or_id s =
  if Hashtbl.mem kw_ht s then ("", s)
  else
    let lcs = String.lowercase_ascii s in
    match Hashtbl.find mixedcase_ht lcs with
      ty -> (ty, lcs)
    | exception Not_found -> ("IDENTIFIER",s)
}



let ws = [' ' '\r' '\n' '\t']
let block_comment = "/*" ([^ '*'] | '*' [^ '/'])* '*'* "*/"
let line_comment = "//" [^ '\r' '\n']*
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = letter (letter | digit | '_' | '-')*
let string_literal = '"' [^ '"']* '"'
let integer_literal = digit+
let floating_point_literal = ('-' | '+')? digit+ '.' digit+


rule _token = parse
| block_comment { _token lexbuf }
| line_comment { _token lexbuf }
| ws+     { _token lexbuf }
| '\r'? '\n' as s { locate lexbuf ("NEWLINE", s) }
| (
"!" | "!=" | "$" | 
"%" | "(" | ")" | "*" | "+" | "," | "-" | "->" | "." | "..." | "/" | 
":" | ":!" | ";" | "<" | "<->" | "<<" | "<=" | "=" | "==" | ">" | ">=" | 
">>" | "[" | "\\" | "\\\\" | "]" | "{" | "|" | "}"
  ) as s { locate lexbuf ("", s) }
| string_literal as s { locate lexbuf ("STRING_LITERAL", s) }
| floating_point_literal as s { locate lexbuf ("FLOATING_POINT_LITERAL", s) }
| integer_literal as s { locate lexbuf ("INTEGER_LITERAL", s) }
| identifier as s { locate lexbuf (kwd_or_id s) }
| eof { locate lexbuf ("EOI","") }

{

let token lb = _token lb

}
