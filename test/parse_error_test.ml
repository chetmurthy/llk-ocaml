
[@@@llk
{foo|
GRAMMAR Extend:
EXTEND g0 ;
EXPORT: etop ;

  e[x]: [ [ f FLAG "foo" -> (f,x) ] ] ;
  etop: [ [ x = e[1] -> x ] ] ;

END;

|foo}
] ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
