open Pa_ppx_testutils ;
open Testutil ;


module Interp = struct
value g = Grammar.gcreate (Plexer.gmake ());
value etop1 = Grammar.Entry.create g "etop1";
value etop2 = Grammar.Entry.create g "etop2";

EXTEND
  GLOBAL: etop1 etop2 ;
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
  e: [ [ n = INT -> n ] ] ;
  e2: [ [ n = UIDENT -> n ] ] ;
  e3: [ [ -> () ] ] ;
  e4: [ [ n = FLOAT -> n ] ] ;

END ;
end ;

[@@@llk
{foo|
GRAMMAR Error1:
  EXPORT: etop1 etop2 ;
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
  e: [ [ n = INT -> n ] ] ;
  e2: [ [ n = UIDENT -> n ] ] ;
  e3: [ [ -> () ] ] ;
  e4: [ [ n = FLOAT -> n ] ] ;
END;

|foo};
];



value matches ?{exact=True} ~{pattern} text =
  let pattern = if exact then Str.quote pattern else pattern in
  match Str.search_forward (Str.regexp pattern) text 0 with [
    _ -> True
  | exception Not_found -> False
]
;

value assert_raises_exn_pattern ?{exact=True} pattern f =
  Testutil.assert_raises_exn_pred
    (fun e ->
      let s = Printexc.to_string e in
      matches ~{exact=exact} ~{pattern=pattern} s)
    f
;

value pa e s = s |> Stream.of_string |> Grammar.Entry.parse e ;

open OUnit2 ;
open OUnitTest ;
value tests = "simple" >::: [
      "Error1" >:: (fun _ -> do {
        assert_raises_exn_pattern "[e] or [e2] or [e3] expected (in [etop1])"
          (fun () -> pa Interp.etop1 {foo|foo a|foo})
      ; assert_raises_exn_pattern {foo|""|foo}
          (fun () -> pa Error1.etop1 {foo|foo a|foo})

      ; assert_raises_exn_pattern "[e] or [e2] or [e3] expected after 'foo' (in [etop2])"
          (fun () -> (pa Interp.etop2 {foo|foo a|foo}))
      ; assert_raises_exn_pattern {foo|""|foo}
          (fun () -> (pa Error1.etop2 {foo|foo a|foo}))

      ; assert_raises_exn_pattern "illegal begin of etop1"
          (fun () -> (pa Interp.etop1 {foo|bar|foo}))
      ; assert_raises_exn_pattern ~{exact=True} ""
          (fun () -> (pa Error1.etop1 {foo|bar|foo}))

      ; assert_raises_exn_pattern "illegal begin of etop2"
          (fun () -> (pa Interp.etop2 {foo|bar|foo}))
      ; assert_raises_exn_pattern "illegal begin of etop2"
          (fun () -> (pa Error1.etop2 {foo|bar|foo}))

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
