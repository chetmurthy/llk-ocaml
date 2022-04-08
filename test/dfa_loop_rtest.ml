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
        | "("; indsp; ")"; "("; arglist; ")"
        | indsp; "("; indsp; ")"; "("; arglist; ")"
        ] ]
    ;
END;

|foo};
] ;
