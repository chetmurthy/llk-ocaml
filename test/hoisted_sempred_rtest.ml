open Pa_ppx_testutils ;
open Testutil ;
open Pa_ppx_base ;

value enableEnum = ref False ;

[@@@llk
{foo|
GRAMMAR Hoisted:
EXPORT:
 stat
 ;

stat: [ [
          identifier -> 1
        | enumAsKeyword -> 2
        ] ]
        ;
identifier: [ [ LIDENT | enumAsID ] ] ;

enumAsKeyword: [ [ {enableEnum.val}? ; "enum" ] ] ;

enumAsID: [ [ {not enableEnum.val}? ; "enum" ] ] ;

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

    "Hoisted" >::: [
      "1" >:: (fun _ -> do {
                 enableEnum.val := False ;
                 assert_equal 1 (pa Hoisted.stat "enum")
              })
    ; "2" >:: (fun _ -> do {
                 enableEnum.val := True ;
                 assert_equal 2 (pa Hoisted.stat "enum")
              })
    ]
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
