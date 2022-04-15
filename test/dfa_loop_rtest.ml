[@@@llk
  {foo|
GRAMMAR DFALoop:
  EXTEND g ;
    EXPORT: arglist_eoi arg1_eoi
    ;
REGEXPS:
  check_indsp = "*"+ ;
  check_indsp_lparen = "*"+ "(" ;
  check_lparen_indsp = "(" "*"+ ;
  check_vardecl = IDENTIFIER | check_indsp IDENTIFIER | check_lparen_indsp IDENTIFIER | check_indsp_lparen check_indsp IDENTIFIER ;
END;
    arglist_eoi: [ [ arglist ] ] ;
    arg1_eoi: [ [ arg1 ] ] ;

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
