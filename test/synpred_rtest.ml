open Pa_ppx_testutils ;
open Testutil ;
open Pa_ppx_base ;

[@@@llk
{foo|
GRAMMAR Syntactic:
EXPORT:
(* e*)
 f
(* g*)
 ;

(*
e: [ [ e1 ; "b" ] ] ;
e1: [ [ e2a | e2b ] ] ;

e2a: [ [ "a" ] ] ;
e2b: [ [ "a" ] ] ;
*)
f: [ [ x = f1 ; ["b1" | "b2"] -> x ] ] ;
f1: [ [ x = f2a -> x | x = f2b -> x ] ] ;

f2a: [ [ (["a"; "b1"])? ; "a" -> 1 ] ] ;
f2b: [ [ (["a"; "b2"])? ; "a" -> 2 ] ] ;
(*
g: [ [ g1 ; "b" ] ] ;
g1: [ [ g2a | g2b ] ] ;

g2a: [ [ "a" ; (["c"; "b"])? ; "c" ] ] ;
g2b: [ [ "a" ; "c" ] ] ;
*)
END ;
|foo} ;
] ;

value matches ~{pattern} text =
  match Str.search_forward (Str.regexp pattern) text 0 with [
    _ -> True
  | exception Not_found -> False
  ]
;

value assert_raises_exn_pattern pattern f =
  Testutil.assert_raises_exn_pred
    (fun e ->
      let s = Printexc.to_string e in
      matches ~{pattern=pattern} s)
    f
;

value pa e s = s |> Stream.of_string |> Grammar.Entry.parse e ;

value loc = Ploc.dummy ;
open OUnit2 ;
open OUnitTest ;
value tests = "simple" >::: [

      "Syntactic" >:: (fun _ -> do {
        assert_equal 1 (pa Syntactic.f "a b1")
      ; assert_equal 2 (pa Syntactic.f "a b2")
      })
]
;

if not Sys.interactive.val then
  run_test_tt_main tests 
else ();
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
