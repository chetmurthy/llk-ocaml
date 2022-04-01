{

let locate ?(comments="") lb v =
  let loc = Ploc.make_unlined (Lexing.lexeme_start lb, Lexing.lexeme_end lb) in
  let loc = Ploc.with_comment loc comments in
  (v, loc)

let kw_ht = Hashtbl.create 23
let _ = ["module";"endmodule"] |> List.iter (fun s -> Hashtbl.add kw_ht s ())
let mixedcase_ht = Hashtbl.create 23
let _ = ["proc";"endproc";"local";"const"
 ;"pers";"var";"tooldata";"wobjdata"
 ;"speeddata";"zonedata";"clock"
 ;"bool"] |> List.iter (fun s -> Hashtbl.add mixedcase_ht s ()) ;;

let kwd_or_id s =
  if Hashtbl.mem kw_ht s then ("", s)
  else
    let lcs = String.lowercase_ascii s in
    if Hashtbl.mem mixedcase_ht lcs then ("",lcs)
    else ("IDENTIFIER",s)
}



let ws = (' ' | '\t' | '\x0c')
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_']
let id = letter ( letter | digit | '-' )*
let comment = '!' [^ '\n'  '\r']*

let escapeSequence = '\\' ('b' | 't' | 'n' | 'f' | 'r' | '"' | '\'' | '\\' | ['0'-'3'] ['0'-'7'] ['0'-'7'] | ['0'-'7']['0'-'7'] | ['0'-'7'])
let charliteral = '\'' (escapeSequence | [^ '\'' '\\' '\r' '\n']) '\''
let stringliteral = '"' (escapeSequence | [^ '\\' '"' '\r' '\n'])* '"'
let exponent = ['e' 'E'] ('+' | '-')? digit+
let floatliteral = digit + '.' digit* exponent? | '.' digit+ exponent? | digit+ exponent

let hexDigit = ['0'-'9' 'a'-'f' 'A'-'F']
let hexPrefix ='\'' ['h' 'H']
let hexSuffix = '\''
let binPrefix = '\'' ['b' 'B']
let binDigit = ('0' | '1')
let binSuffix = '\''
let intliteral = digit + | hexPrefix hexDigit+ hexSuffix | binPrefix binDigit+ binSuffix

rule _token = parse
| comment { _token lexbuf }
| ws+     { _token lexbuf }
| '\r'? '\n' as s { locate lexbuf ("NEWLINE", s) }
| (['t' 'T']['r' 'R']['u' 'U']['e' 'E'] | ['f' 'F']['a' 'A']['l' 'L']['s' 'S']['e' 'E']) as s { locate lexbuf ("BOOLLITERAL", s) }
| ("/"|":="|","|"{"|"}"|
   ":"|";"|"("|")"|"["|"]"|
   "."|".."|">"|">="|"<"|"<="|
   "=="|"<>"|"+"|"-"|"*"|"%"|"#") as s { locate lexbuf ("", s) }
| charliteral as s { locate lexbuf ("CHARLITERAL", s) }
| stringliteral as s { locate lexbuf ("STRINGLITERAL", s) }
| floatliteral as s { locate lexbuf ("FLOATLITERAL", s) }
| intliteral as s { locate lexbuf ("INTLITERAL", s) }
| '\\' ['o' 'O']['n' 'N'] as s { locate lexbuf ("ON_CALL", s) }
| '\\' ['o' 'O']['f' 'F']['f' 'F'] as s { locate lexbuf ("OFF_CALL", s) }
| id as s { locate lexbuf (kwd_or_id s) }
| eof { locate lexbuf ("EOI","") }

{

let token lb = _token lb

}
