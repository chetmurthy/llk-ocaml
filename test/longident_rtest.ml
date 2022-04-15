open Pa_ppx_testutils ;
open Testutil ;
open Pa_ppx_base ;

[@@@llk
{foo|
GRAMMAR Longident:
EXPORT: longident longident_eoi expr expr_eoi expr_longident;
REGEXPS:
  check_dot_uid =  "." (UIDENT | $uid | $_uid) ;
END;

  longident:
    [ [ i = V UIDENT "uid" ;
        l = LIST0 [ (["." ; V UIDENT])? ; "." ; i' = V UIDENT "uid" -> i' ] ->
        List.fold_left (fun li i -> <:extended_longident< $longid:li$ . $_uid:i$ >>)
        <:extended_longident< $_uid:i$ >> l
      ] ]
      ;
(*
  longident:
    [ NONGREEDY LEFTA
      [ me1 = SELF ; (["."; V UIDENT "uid"])?  ; "."; i = V UIDENT "uid" → <:extended_longident< $longid:me1$ . $_uid:i$ >> ]
    | [ i = V UIDENT "uid" → <:extended_longident< $_uid:i$ >>
      ] ]
  ;
*)
  longident_eoi: [ [ x = longident ; EOI -> x ] ] ;

  expr: [
    "apply" LEFTA
      [ e1 = SELF; e2 = SELF → <:expr< $e1$ $e2$ >> ]
  | "simple"
      [ "." -> <:expr< . >>
      | e = expr_longident → e
      | s = LIDENT → <:expr< $lid:s$ >>
      ]
  ]
  ;
  expr_longident:
    [
      [ li = longident -> <:expr< $longid:li$ >>
      | li = longident ; PRIORITY 1 ; "." ; "(" ; e = expr ; ")" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; PRIORITY 1 ; "." ; id = V LIDENT "lid" ->
        <:expr< $longid:li$ . $_lid:id$ >>
      ]
    ]
  ;

  expr_eoi: [ [ x = expr ; EOI -> x ] ] ;
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

      "Longident" >:: (fun _ -> do {
        assert_equal ~{cmp=Reloc.eq_longid} <:longident< A.B.C >> (pa Longident.longident_eoi "A.B.C")
      ; assert_equal ~{cmp=Reloc.eq_expr} <:expr< A.B.c >> (pa Longident.expr_eoi "A.B.c")
      ; assert_equal ~{cmp=Reloc.eq_expr}
          (Ppxutil.Expr.applist <:expr< A.B.c >> [<:expr< . >>; <:expr< d >>])
          (pa Longident.expr_eoi "A.B.c.d")
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
