(* camlp5r *)
(* alef.ml,v *)

value input_file = ref "" ;
value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;

value lexer = Plexing.lexer_func_of_ocamllex_located Aleflexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;

value loc_strip_comment loc = Ploc.with_comment loc "" ;

[@@@llk
{foo|
GRAMMAR Alef:
  EXTEND g ;
    EXPORT: program program_eoi decllist decl zargs ztname adtfunc typespec ztag zpolytype polytype setlist
      sname name memberlist vardecllist ivardecl zinit zelist vardecl arrayspec indsp arglist
      arglistp arg tuplearg autolist autodecl block slist tbody ctlist tcase cbody clist case_ rbody
      zlab stmnt info nlstmnt zconst zexpr expr_ castexpr typecast monexpr ztelist telist tcomp
      term_ stag zarlist elist tlist tname variant xtname bufdim sclass typename enum_member;
REGEXPS:
  check_indsp = "*"+ ;
  check_indsp_lparen = "*"+ "(" ;
  check_lparen_indsp = "(" "*"+ ;
  check_vardecl = IDENTIFIER | check_indsp IDENTIFIER | check_lparen_indsp IDENTIFIER | check_indsp_lparen check_indsp IDENTIFIER ;
END;
    
    program_eoi: [ [ x = program ; EOI -> x ] ] ;
    
    program:
      
      [ [ GREEDY OPT decllist ] ]
    ;
    decllist:
      
      [ [ GREEDY LIST1 decl ] ]
    ;
    decl:
      
      [ [ tname; GREEDY OPT vardecllist; ";"
        | tname; vardecl; "("; GREEDY OPT arglist; ")"; block
        | tname; adtfunc; "("; GREEDY OPT arglist; ")"; block
        | tname; vardecl; "("; GREEDY OPT arglist; ")"; ";"
        | typespec; ";"
        | "typedef"; ztname; vardecl; GREEDY OPT zargs; ";"
        | "typedef"; IDENTIFIER; ";" ] ]
    ;
    zargs:
      
      [ [ "("; GREEDY OPT arglist; ")" ] ]
    ;
    ztname:
      
      [ [ tname
        | "aggr"
        | "adt"
        | "union" ] ]
    ;
    adtfunc:
      
      [ [ typename; "."; name
        | indsp; typename; "."; name ] ]
    ;
    typespec:
      
      [ [ "aggr"; GREEDY OPT ztag; "{"; memberlist; "}"; GREEDY OPT ztag
        | "union"; GREEDY OPT ztag; "{"; memberlist; "}"; GREEDY OPT ztag
        | "adt"; GREEDY OPT ztag; GREEDY OPT zpolytype; "{"; memberlist; "}"; GREEDY OPT ztag
        | "enum"; GREEDY OPT ztag; "{"; setlist; "}" ] ]
    ;
    ztag:
      
      [ [ name
        | typename ] ]
    ;
    zpolytype:
      
      [ [ "["; polytype; "]" ] ]
    ;
    polytype:
      
      [ [ name
        | name; ","; polytype ] ]
    ;
    setlist:
      
      [ [ GREEDY OPT sname
        | setlist; ","; setlist ] ]
    ;
    sname:
      
      [ [ name; GREEDY OPT [ "="; expr_ ] ] ]
    ;
    name:
      
      [ [ IDENTIFIER ] ]
    ;
    memberlist:
      
      [ [ decl
        | memberlist; decl ] ]
    ;
    vardecllist:
      
      [ [ ivardecl; GREEDY LIST0 [ ","; ivardecl ] ] ]
    ;
    ivardecl:
      
      [ [ vardecl; GREEDY OPT zinit ] ]
    ;
    zinit:
      
      [ [ "="; zelist ] ]
    ;
    zelist:
      
      [ [ GREEDY OPT zexpr
        | "["; expr_; "]"; expr_
        | "."; stag; expr_
        | "{"; zelist; "}"
        | "["; expr_; "]"; "{"; zelist; "}"
        | zelist; ","; zelist ] ]
    ;
    vardecl:
      
      [ [ IDENTIFIER; GREEDY OPT arrayspec
        | indsp; IDENTIFIER; GREEDY OPT arrayspec
        | "("; indsp; IDENTIFIER; GREEDY OPT arrayspec; ")"; "("; GREEDY OPT arglist; ")"
        | indsp; "("; indsp; IDENTIFIER; GREEDY OPT arrayspec; ")"; "("; GREEDY OPT arglist; ")" ] ]
    ;
    arrayspec:
      
      [ [ GREEDY LIST1 [ "["; GREEDY OPT zexpr; "]" ] ] ]
    ;
    indsp:
      
      [ [ GREEDY LIST1 "*" ] ]
    ;
    arglist:
      
      [ [ GREEDY LIST0 arglistp; ","; arg ] ]
    ;
    arglistp:
      
      [ [ arg
        | "*"; xtname
        | "."; xtname ] ]
    ;
    arg:
      
      [ [ xtname
        | xtname; check_indsp; indsp; GREEDY OPT arrayspec
        | xtname; check_lparen_indsp; "("; indsp; ")"; "("; GREEDY OPT arglist; ")"
        | xtname; check_indsp_lparen; indsp; "("; indsp; ")"; "("; GREEDY OPT arglist; ")"
        | "tuple"; tuplearg
        | xtname; check_vardecl ; vardecl
        | "."; "."; "." ] ]
    ;
    tuplearg:
      
      [ [ tname
        | tname; "("; indsp; ")"; "("; GREEDY OPT arglist; ")"
        | tname; vardecl ] ]
    ;
    autolist:
      
      [ [ GREEDY LIST1 autodecl ] ]
    ;
    autodecl:
      
      [ [ xtname; GREEDY OPT vardecllist; ";"
        | "tuple"; tname; GREEDY OPT vardecllist; ";" ] ]
    ;
    block:
      
      [ [ "{"; GREEDY OPT autolist; GREEDY OPT slist; "}"
        | "!"; "{"; GREEDY OPT autolist; GREEDY OPT slist; "}" ] ]
    ;
    slist:
      
      [ [ GREEDY LIST1 stmnt ] ]
    ;
    tbody:
      
      [ [ "{"; GREEDY OPT ctlist; "}"
        | "!"; "{"; GREEDY OPT clist; "}" ] ]
    ;
    ctlist:
      
      [ [ GREEDY LIST1 tcase ] ]
    ;
    tcase:
      
      [ [ "case"; typecast; ":"; GREEDY OPT slist
        | "default"; ":"; GREEDY OPT slist ] ]
    ;
    cbody:
      
      [ [ "{"; GREEDY OPT clist; "}"
        | "!"; "{"; GREEDY OPT clist; "}" ] ]
    ;
    clist:
      
      [ [ GREEDY LIST1 case_ ] ]
    ;
    case_:
      
      [ [ "case"; expr_; ":"; GREEDY OPT slist
        | "default"; ":"; GREEDY OPT slist ] ]
    ;
    rbody:
      
      [ [ stmnt
        | IDENTIFIER; block ] ]
    ;
    zlab:
      
      [ [ IDENTIFIER ] ]
    ;
    stmnt:
      
      [ [ nlstmnt
        | IDENTIFIER; ":"; stmnt ] ]
    ;
    info:
      
      [ [ ","; STRING_CONST ] ]
    ;
    nlstmnt:
      
      [ [ GREEDY OPT zexpr; ";"
        | block
        | "check"; expr_; GREEDY OPT info; ";"
        | "alloc"; elist; ";"
        | "unalloc"; elist; ";"
        | "rescue"; rbody
        | "raise"; GREEDY OPT zlab; ";"
        | "goto"; IDENTIFIER; ";"
        | "proc"; elist; ";"
        | "task"; elist; ";"
        | "become"; expr_; ";"
        | "alt"; cbody
        | "return"; GREEDY OPT zexpr; ";"
        | "for"; "("; GREEDY OPT zexpr; ";"; GREEDY OPT zexpr; ";"; GREEDY OPT zexpr; ")"; stmnt
        | "while"; "("; expr_; ")"; stmnt
        | "do"; stmnt; "while"; "("; expr_; ")"
        | "if"; "("; expr_; ")"; stmnt
        | "if"; "("; expr_; ")"; stmnt; "else"; stmnt
        | "par"; block
        | "switch"; expr_; cbody
        | "typeof"; expr_; tbody
        | "continue"; GREEDY OPT zconst; ";"
        | "break"; GREEDY OPT zconst; ";" ] ]
    ;
    zconst:
      
      [ [ CONSTANT ] ]
    ;
    zexpr:
      
      [ [ expr_ ] ]
    ;
    expr_:
      
      [ [ castexpr
        | expr_; "*"; expr_
        | expr_; "/"; expr_
        | expr_; "%"; expr_
        | expr_; "+"; expr_
        | expr_; "-"; expr_
        | expr_; ">>"; expr_
        | expr_; "<<"; expr_
        | expr_; "<"; expr_
        | expr_; ">"; expr_
        | expr_; "<="; expr_
        | expr_; ">="; expr_
        | expr_; "=="; expr_
        | expr_; "!="; expr_
        | expr_; "&"; expr_
        | expr_; "^"; expr_
        | expr_; "|"; expr_
        | expr_; "&&"; expr_
        | expr_; "||"; expr_
        | expr_; "="; expr_
        | expr_; ":="; expr_
        | expr_; "<-"; "="; expr_
        | expr_; "+="; expr_
        | expr_; "-="; expr_
        | expr_; "*="; expr_
        | expr_; "/="; expr_
        | expr_; "%="; expr_
        | expr_; ">>="; expr_
        | expr_; "<<="; expr_
        | expr_; "&="; expr_
        | expr_; "|="; expr_
        | expr_; "^="; expr_
        | expr_; "::"; expr_ ] ]
    ;
    castexpr:
      
      [ [ monexpr
        | "("; typecast; ")"; castexpr
        | "("; "alloc"; typecast; ")"; castexpr ] ]
    ;
    typecast:
      
      [ [ xtname
        | xtname; indsp
        | xtname; "("; indsp; ")"; "("; GREEDY OPT arglist; ")"
        | "tuple"; tname ] ]
    ;
    monexpr:
      
      [ [ term_
        | "*"; castexpr
        | "&"; castexpr
        | "+"; castexpr
        | "-"; castexpr
        | "--"; castexpr
        | "zerox"; castexpr
        | "++"; castexpr
        | "!"; castexpr
        | "~"; castexpr
        | "sizeof"; monexpr
        | "<-"; castexpr
        | "?"; castexpr ] ]
    ;
    ztelist:
      
      [ [ telist ] ]
    ;
    telist:
      
      [ [ tcomp; GREEDY LIST0 [ ","; tcomp ] ] ]
    ;
    tcomp:
      
      [ [ expr_
        | "{"; GREEDY OPT ztelist; "}" ] ]
    ;
    term_:
      
      [ [ "("; telist; ")"
        | "sizeof"; "("; typecast; ")"
        | term_; "("; GREEDY OPT zarlist; ")"
        | term_; "["; expr_; "]"
        | term_; "."; stag
        | "."; typename; "."; stag
        | term_; "->"; stag
        | term_; "--"
        | term_; "++"
        | term_; "?"
        | name
        | "."; "."; "."
        | ARITHMETIC_CONST
        | "nil"
        | CONSTANT
        | enum_member
        | STRING_CONST
        | "$"; STRING_CONST ] ]
    ;
    stag:
      
      [ [ IDENTIFIER
        | typename ] ]
    ;
    zarlist:
      
      [ [ elist ] ]
    ;
    elist:
      
      [ [ expr_
        | elist; ","; expr_ ] ]
    ;
    tlist:
      
      [ [ typecast
        | typecast; ","; tlist ] ]
    ;
    tname:
      
      [ [ GREEDY OPT sclass; xtname
        | GREEDY OPT sclass; "tuple"; "("; tlist; ")"
        | GREEDY OPT sclass; "("; tlist; ")" ] ]
    ;
    variant:
      
      [ [ typecast
        | typecast; ","; variant ] ]
    ;
    xtname:
      
      [ [ "int"
        | "uint"
        | "sint"
        | "usint"
        | "byte"
        | "float"
        | "void"
        | typename
        | typename; "["; variant; "]"
        | "chan"; "("; variant; ")"; GREEDY OPT bufdim ] ]
    ;
    bufdim:
      
      [ [ "["; expr_; "]" ] ]
    ;
    sclass:
      
      [ [ "extern"
        | "intern"
        | "private" ] ]
    ;
    typename:
      
      [ [ IDENTIFIER ] ]
    ;
    enum_member:
      
      [ [ IDENTIFIER ] ]
    ;
END;

|foo};
] ;

value parse_program_eoi = Grammar.Entry.parse Alef.program_eoi ;

if not Sys.interactive.val then
try
  let (ic, ifname) = match Sys.argv.(1) with [
      x -> (open_in x, x)
    | exception (Invalid_argument _) -> (stdin, "<stdin>")
  ] in do {
    Aleflexer.input_file.val := ifname ;
    let g = parse_program_eoi (Stream.of_channel ic) in
    print_string "OK\n"
  }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
