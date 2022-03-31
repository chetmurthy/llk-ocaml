open Pa_ppx_testutils ;
open Testutil ;


module Interp = struct
value g = Grammar.gcreate (Plexer.gmake ());
value etop1 = Grammar.Entry.create g "etop1";
value etop2 = Grammar.Entry.create g "etop2";
value etop3 = Grammar.Entry.create g "etop3";

EXTEND
  GLOBAL: etop1 etop2 etop3 ;
  etop1: [ [
            FLAG "foo" ; x = e -> x
          | FLAG "foo" ; x = e2 -> x
          | FLAG "foo" ; x = e3 ; y = e4 -> y
          ] ];
  etop2: [ [
            "foo" ; x = e -> x
          | "foo" ; x = e2 -> x
          | "foo" ; x = e3 ; y = e4 -> y
          ] ];
  etop3: [ [
            "foo" ; x = e5 ; "bar" -> x
          ] ];
  e: [ [ n = INT -> n ] ] ;
  e2: [ [ n = UIDENT -> n ] ] ;
  e3: [ [ -> () ] ] ;
  e4: [ [ n = FLOAT -> n ] ] ;
  e5: [ [ n = INT -> Some n | -> None ] ] ;

END ;
end ;

[@@@llk
{foo|
GRAMMAR Error1:
  EXPORT: etop1 etop2 etop3 ;
  etop1: [ [
            FLAG "foo" ; x = e -> x
          | FLAG "foo" ; x = e2 -> x
          | FLAG "foo" ; x = e3 ; y = e4 -> y
          ] ];
  etop2: [ [
            "foo" ; x = e -> x
          | "foo" ; x = e2 -> x
          | "foo" ; x = e3 ; y = e4 -> y
          ] ];
  etop3: [ [
            "foo" ; x = e5 ; "bar" -> x
          ] ];

  e: [ [ n = INT -> n ] ] ;
  e2: [ [ n = UIDENT -> n ] ] ;
  e3: [ [ -> () ] ] ;
  e4: [ [ n = FLOAT -> n ] ] ;
  e5: [ [ n = INT -> Some n | -> None ] ] ;
END;

|foo};
];



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

value pa e s = s |> Stream.of_string |> Grammar.Entry.parse e ;

open OUnit2 ;
open OUnitTest ;
value tests = "simple" >::: [
      "Error1" >:: (fun _ -> do {
        assert_raises_exn_pattern "[e] or [e2] or [e3] expected (in [etop1])"
          (fun () -> pa Interp.etop1 {foo|foo a|foo})
      ; assert_raises_exn_pattern
{foo|[x__0001 = etop1__0001] expected after [etop1__0002]|foo}
(*
 {foo|[x = e] or [x = e2] or [x = e3]|foo}
 *)
          (fun () -> pa Error1.etop1 {foo|foo a|foo})

      ; assert_raises_exn_pattern "[e] or [e2] or [e3] expected after 'foo' (in [etop2])"
          (fun () -> (pa Interp.etop2 {foo|foo a|foo}))
      ; assert_raises_exn_pattern
{foo|[x__0002 = etop2__0001] expected after ['foo']|foo}
(*
 {foo|[x = e] or [x = e2] or [x = e3] expected after ['foo'] (in [etop2])|foo}
 *)
          (fun () -> (pa Error1.etop2 {foo|foo a|foo}))

      ; assert_raises_exn_pattern "illegal begin of etop1"
          (fun () -> (pa Interp.etop1 {foo|bar|foo}))
      ; assert_raises_exn_pattern ~{quote=True} ""
          (fun () -> (pa Error1.etop1 {foo|bar|foo}))

      ; assert_raises_exn_pattern "illegal begin of etop2"
          (fun () -> (pa Interp.etop2 {foo|bar|foo}))
      ; assert_raises_exn_pattern "illegal begin of etop2"
          (fun () -> (pa Error1.etop2 {foo|bar|foo}))

      ; assert_raises_exn_pattern "[e5] expected after 'foo' (in [etop3])"
          (fun () -> (pa Interp.etop3 {foo|foo goo|foo}))
      ; assert_raises_exn_pattern "[x = e5] expected after ['foo'] (in [etop3])"
          (fun () -> (pa Error1.etop3 {foo|foo goo|foo}))

      })
]
;

if not Sys.interactive.val then
  run_test_tt_main tests
else () ;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
