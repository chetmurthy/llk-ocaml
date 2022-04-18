open Pa_ppx_testutils ;
open Testutil ;
open Pa_ppx_base ;

value enableEnum = ref False ;

[@@@llk
{foo|
GRAMMAR Hoisted:
EXPORT:
 stat dynamically_stat dynamically_id dynamically_kwd
 ;

stat: [ [
          identifier -> 1
        | enumAsKeyword -> 2
        ] ]
        ;
identifier: [ [ s = LIDENT -> s | s = enumAsID -> s ] ] ;

enumAsKeyword: [ [ {enableEnum.val}? ; s = "enum" -> s ] ] ;

enumAsID: [ [ {not enableEnum.val}? ; s = "enum" -> s ] ] ;

set_reference: [ [ "set" ; !! -> enableEnum.val := True | "unset" ; !! -> enableEnum.val := False ] ] ;

dynamically_stat: [ [ set_reference ; s = stat -> s ] ] ;
dynamically_id: [ [ set_reference ; s = identifier -> s ] ] ;
dynamically_kwd: [ [ set_reference ; s = enumAsKeyword -> s ] ] ;

END ;
|foo} ;
] ;

value matches ?{quote=True} ~{pattern} text =
  let pattern = if quote then Str.quote pattern else pattern in
  match Str.search_forward (Str.regexp pattern) text 0 with [
    _ -> True
  | exception Not_found -> False
]
;

value assert_raises_exn_pattern ?{quote=True} pattern f =
  Testutil.assert_raises_exn_pred
    (fun e ->
      let s = Printexc.to_string e in
      matches ~{quote=quote} ~{pattern=pattern} s)
    f
;

value assert_raises_exn ?{quote=True} exn f =
  Testutil.assert_raises_exn_pred
    (fun exn' ->
      let s = Printexc.to_string exn in
      let s' = Printexc.to_string exn' in
      s = s')
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
    ; "3" >:: (fun _ -> do {
                 assert_equal 2 (pa Hoisted.dynamically_stat "set enum")
              })
    ; "4" >:: (fun _ -> do {
                 assert_equal 1 (pa Hoisted.dynamically_stat "unset enum")
              })
    ; "5" >:: (fun _ -> do {
                 assert_raises_exn_pattern
                   "[s = identifier] expected"
                   (fun () -> pa Hoisted.dynamically_id "set enum")
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
