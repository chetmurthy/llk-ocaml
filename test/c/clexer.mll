{

let input_file = ref "" ;;

let locate ?(comments="") lb v =
  let loc = Ploc.make_loc !input_file 1 0 (Lexing.lexeme_start lb, Lexing.lexeme_end lb) comments in
  (v, loc)

let kw_ht = Hashtbl.create 23
let _ = ["auto"; "break"; "case"; "char"; "const"; "continue"; "default"; 
"do"; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; 
"int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"; 
"struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; 
"while"] |> List.iter (fun s -> Hashtbl.add kw_ht s ())
let mixedcase_ht = Hashtbl.create 23
let _ = []
        |> List.iter (fun (ty,s) -> Hashtbl.add mixedcase_ht s ty) ;;

let kwd_or_id s =
  if Hashtbl.mem kw_ht s then ("", s)
  else
    let lcs = String.lowercase_ascii s in
    match Hashtbl.find mixedcase_ht lcs with
      ty -> (ty, lcs)
    | exception Not_found -> ("IDENTIFIER",s)
}

let block_comment = "/*" ([^ '*'] | '*' [^ '/'])* '*'* "*/"
let line_comment = "//" [^ '\r' '\n']*
let line_command = '#' [^ '\r' '\n']* '\r'? '\n'
let comment = (block_comment | line_comment)
let ws = (' '|'\r'|'\t'|'\x0c'|'\n')+
let hexDigit = ['0'-'9' 'a'-'f' 'A'-'F']
let unicodeEscape = '\\' 'u' hexDigit hexDigit hexDigit hexDigit
let octalEscape = '\\' ['0'-'3'] ['0'-'7'] ['0'-'7']
    |   '\\' ['0'-'7'] ['0'-'7']
    |   '\\' ['0'-'7']

let escapeSequence = '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\') | octalEscape

let floatTypeSuffix = ('f'|'F'|'d'|'D')

let digit = ['0'-'9']
let exponent = ('e'|'E') ('+'|'-')? digit+


let _FLOATING_POINT_LITERAL =
       digit+ '.' digit* exponent? floatTypeSuffix?
    |   '.' digit+ exponent? floatTypeSuffix?
    |   digit+ exponent floatTypeSuffix?
    |   digit+ exponent? floatTypeSuffix

let integerTypeSuffix =
	('u'|'U')? ('l'|'L')
	('u'|'U')  ('l'|'L')?


let _HEX_LITERAL = '0' ('x'|'X') hexDigit+ integerTypeSuffix?
let _DECIMAL_LITERAL = ('0' | ['1'-'9'] digit*) integerTypeSuffix?
let _OCTAL_LITERAL = '0' ['0'-'7']+ integerTypeSuffix?

let _CHARACTER_LITERAL = '\'' ( escapeSequence | [^ '\'' '\\'] ) '\''
let _STRING_LITERAL = '"' ( escapeSequence | [^ '\\' '"'] )* '"'
	
let _LETTER = '$' | ['A'-'Z'] |	['a'-'z'] | '_'
let _IDENTIFIER = _LETTER (_LETTER|digit)*



let special = (
"!" | "!=" | "%" | "%=" | "&" | "&&" | "&=" | "(" | 
")" | "*" | "*=" | "+" | "++" | "+=" | "," | "-" | "--" | "-=" | "->" | 
"." | "..." | "/" | "/=" | ":" | ";" | "<" | "<<" | "<<=" | "<=" | "=" | 
"==" | ">" | ">=" | ">>" | ">>=" | "?" | "[" | "]" | "^" | "^=" | "{" | 
"|" | "|=" | "||" | "}" | "~"
)

rule _token = parse
| comment { _token lexbuf }
| line_command { _token lexbuf }
| ws     { _token lexbuf }
| _FLOATING_POINT_LITERAL as s { locate lexbuf ("FLOATING_POINT_LITERAL", s) }
| _HEX_LITERAL as s { locate lexbuf ("HEX_LITERAL", s) }
| _DECIMAL_LITERAL as s { locate lexbuf ("DECIMAL_LITERAL", s) }
| _OCTAL_LITERAL as s { locate lexbuf ("OCTAL_LITERAL", s) }
| _CHARACTER_LITERAL as s { locate lexbuf ("CHARACTER_LITERAL", s) }
| _STRING_LITERAL as s { locate lexbuf ("STRING_LITERAL", s) }

| _IDENTIFIER as s { locate lexbuf (kwd_or_id s) }
| special { locate lexbuf ("",Lexing.lexeme lexbuf) }
| eof { locate lexbuf ("EOI","") }

{

let token lb = _token lb

}
