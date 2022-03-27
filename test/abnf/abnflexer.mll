{

let locate ?(comments="") lb v =
  let loc = Ploc.make_unlined (Lexing.lexeme_start lb, Lexing.lexeme_end lb) in
  let loc = Ploc.with_comment loc comments in
  (v, loc)

}

let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let digit = ['0'-'9']
let bit = ['0'-'1']
let letter = ['a'-'z' 'A'-'Z']
let string = ( "%s" | "%i" )? '"' ( [^ '"'] )* '"'
let ws = ( ' ' | '\t' | '\r' | '\n' )
let comment = ';' [^ '\n'  '\r']* '\r'? '\n'
let int = ['0'-'9']+
let id = letter ( letter | digit | '-' )*
let proseValue = '<' ( [^ '>'] )* '>'
let hexValue =  'x' hex_digit+ ( ( '.' hex_digit+ )+ | ( '-' hex_digit+ ) )?
let decimalValue = 'd' digit+ ( ( '.' digit+ )+ | ( '-' digit+ ) )?
let binaryValue = 'b' bit+ ( ( '.' bit+ )+ | ( '-' bit+ ) )?
let numberValue = '%' ( binaryValue | decimalValue | hexValue )

rule _token = parse
| comment { _token lexbuf }
| ws     { _token lexbuf }
| string as s { locate lexbuf ("STRING", s) }
| int as s { locate lexbuf ("INT", s) }
| id as s { locate lexbuf ("ID", s) }
| proseValue as s { locate lexbuf ("PROSEVALUE", s) }
| numberValue as s { locate lexbuf ("NUMBERVALUE", s) }
| "[" { locate lexbuf ("","[") }
| "]" { locate lexbuf ("","]") }
| "(" { locate lexbuf ("","(") }
| ")" { locate lexbuf ("",")") }
| "*" { locate lexbuf ("","*") }
| "/" { locate lexbuf ("","/") }
| "%" { locate lexbuf ("","%") }
| "=" { locate lexbuf ("","=") }
| eof { locate lexbuf ("EOI","") }

{

let token lb = _token lb

}
