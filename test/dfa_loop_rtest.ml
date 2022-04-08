[@@@llk
  {foo|
GRAMMAR DFALoop:
  EXTEND g ;
    EXPORT: arglist arg1
    ;
REGEXPS:
  check_indsp = "*"+ ;
  check_indsp_lparen = "*"+ "(" ;
  check_lparen_indsp = "(" "*"+ ;
  check_vardecl = IDENTIFIER | check_indsp IDENTIFIER | check_lparen_indsp IDENTIFIER | check_indsp_lparen check_indsp IDENTIFIER ;
END;

    vardecl:
      [ [ IDENTIFIER; arrayspec
        | indsp; IDENTIFIER; arrayspec
        | "("; indsp; IDENTIFIER; arrayspec; ")"; "("; ")"
        | indsp; "("; indsp; IDENTIFIER; arrayspec; ")"; "("; ")" ] ]
    ;
    arrayspec: [ [ "[" ; "]" ] ] ;
    indsp: [ [ GREEDY LIST1 "*" ] ] ;
    arglist: [ [ GREEDY LIST0 arglistp; ","; arg1 ] ]  ;
    arglistp:
      [ [ arg1
        | "*"
        | "." ] ]
    ;
    arg1:

      [ [ 
          -> ()
        | indsp; arrayspec
        | "("; indsp; ")"; "("; arglist; ")"
        | indsp; "("; indsp; ")"; "("; arglist; ")"
        | vardecl ] ]
    ;
END;

|foo};
] ;
