open Pa_ppx_testutils ;
open Testutil ;
open Pa_ppx_base ;


[@@@llk
{foo|
GRAMMAR Unused:
EXPORT: e1 e2__0002;

e1: [ [ e2__0001 ] ] ;

e2__0001: [ [ e2__0002 ] ] ;

e2__0002: [ [ e2__0003 ] ] ;

e2__0003: [ [ "foo" ] ] ;

END ;
|foo} ;
] ;
