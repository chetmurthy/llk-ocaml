(* camlp5r *)
(* r2official_test.ml *)

open Pa_ppx_testutils ;
open Testutil;
open Testutil2;
open Papr_util ;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;


module Official = struct
include Papr_util.Official ;
module Implem = struct
value pr l =
  Pr_official.(with_buffer_formatter pp_implem (l, Ploc.dummy))
;
end ;
module Interf = struct
value pr l =
  Pr_official.(with_buffer_formatter pp_interf (l, Ploc.dummy))
;
end ;
value both_pa = Official.both_pa ;
value both_pr = (Implem.pr, Interf.pr) ;
end ;

value both_pa1 =
  let open Revised_rtest.Revised in
  let pa pf input_file strm = let (ast, _) = with_input_file input_file pf strm in ast in
  let pa1 pf input_file s = let ast = pf input_file (Stream.of_string s) in ast in
  let implem_pa1 = pa1 (pa (Grammar.Entry.parse implem)) in
  let interf_pa1 = pa1 (pa (Grammar.Entry.parse interf)) in
  (implem_pa1, interf_pa1)
;

value tests = "matrix" >::: (Papr_test_matrix.r2official both_pa1 Official.both_pr (Some Official.both_pa) ()) ;


value _ =
if not Sys.interactive.val then
  run_test_tt_main tests
else ()
;  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
