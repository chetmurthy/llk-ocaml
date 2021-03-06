{

let input_file = ref "" ;;

let locate ?(comments="") lb v =
  let loc = Ploc.make_loc !input_file 1 0 (Lexing.lexeme_start lb, Lexing.lexeme_end lb) comments in
  (v, loc)

let kw_ht = Hashtbl.create 23
let _ = ["char"; "for"; "int"] |> List.iter (fun s -> Hashtbl.add kw_ht s ())
let mixedcase_ht = Hashtbl.create 23
let _ = []
        |> List.iter (fun (ty,s) -> Hashtbl.add mixedcase_ht s ty) ;;

let kwd_or_id s =
  if Hashtbl.mem kw_ht s then ("", s)
  else
    let lcs = String.lowercase_ascii s in
    match Hashtbl.find mixedcase_ht lcs with
      ty -> (ty, lcs)
    | exception Not_found -> ("ID",s)
}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ws = ( ' ' | '\t' | '\r' | '\n' )+
let int = ['0'-'9']+
let id = (letter | '_') ( letter | digit | '_' )*
let block_comment = "/*" ([^ '*'] | '*' [^ '/'])* '*'* "*/"
let line_comment = "//" [^ '\r' '\n']*
let comment = (block_comment | line_comment)
let special = (
"(" | ")" | "+" | "," | ";" | 
"<" | "=" | "==" | "{" | "}"
)

rule _token = parse
| comment { _token lexbuf }
| ws     { _token lexbuf }
| int as s { locate lexbuf ("INT", s) }
| id as s { locate lexbuf (kwd_or_id s) }
| special { locate lexbuf ("",Lexing.lexeme lexbuf) }
| eof { locate lexbuf ("EOI","") }

{

let token lb = _token lb

}
