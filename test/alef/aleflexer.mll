{

let input_file = ref "" ;;

let locate ?(comments="") lb v =
  let loc = Ploc.make_loc !input_file 1 0 (Lexing.lexeme_start lb, Lexing.lexeme_end lb) comments in
  (v, loc)

let kw_ht = Hashtbl.create 23
let _ = [
"adt"; "aggr"; "alloc"; "alt"; "become"; "break"; "byte"; 
"case"; "chan"; "check"; "continue"; "default"; "do"; "else"; "enum"; 
"extern"; "float"; "for"; "goto"; "if"; "int"; "intern"; "lint"; "nil"; 
"par"; "private"; "proc"; "raise"; "rescue"; "return"; "sint"; "sizeof"; 
"switch"; "task"; "tuple"; "typedef"; "typeof"; "uint"; "ulint"; "unalloc"; 
"union"; "usint"; "void"; "while"; "zerox"
  ] |> List.iter (fun s -> Hashtbl.add kw_ht s ())

let kwd_or_id s =
  if Hashtbl.mem kw_ht s then ("", s)
  else ("IDENTIFIER",s)
}



let ws = [' ' '\r' '\n' '\t']+
let digit = ['0'-'9']
let arithmetic_const =  digit+ ('.' digit*)? ('e' digit+)?
let constant = '\'' [^ '\'']* '\''
let string_const = '"' [^ '"']* '"'
let identifier = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule _token = parse
| ws     { _token lexbuf }
| (
"!" | "!=" | "$" | 
"%" | "%=" | "&" | "&&" | "&=" | "(" | ")" | "*" | "*=" | "+" | "++" | 
"+=" | "," | "-" | "--" | "-=" | "->" | "." | "/" | "/=" | ":" | "::" | 
":=" | ";" | "<" | "<-" | "<<" | "<<=" | "<=" | "=" | "==" | ">" | ">=" | 
">>" | ">>=" | "?" | "[" | "]" | "^" | "^=" | "{" | "|" | "|=" | "||" | 
"}" | "~"
  ) as s { locate lexbuf ("", s) }
| arithmetic_const as s { locate lexbuf ("ARITHMETIC_CONST", s) }
| constant as s { locate lexbuf ("CONSTANT", s) }
| string_const as s { locate lexbuf ("STRING_CONST", s) }
| identifier as s { locate lexbuf (kwd_or_id s) }
| eof { locate lexbuf ("EOI","") }

{

let token lb = _token lb

}
