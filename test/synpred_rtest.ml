open Pa_ppx_testutils ;
open Testutil ;
open Pa_ppx_base ;

[@@@llk
{foo|
GRAMMAR Syntactic:
EXPORT: e f;

e: [ [ e1 ; "b" ] ] ;
e1: [ [ e2a | e2b ] ] ;

e2a: [ [ "a" ] ] ;
e2b: [ [ "a" ] ] ;


f: [ [ f1 ; "b" ] ] ;
f1: [ [ (["a"; "b"])? ; e2a | e2b ] ] ;


END ;
|foo} ;
] ;
