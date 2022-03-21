(* camlp5r *)
(* o2official_test.ml *)

open Pa_ppx_testutils ;
open Testutil;
open Testutil2;
open Papr_util ;

open OUnit2;
open OUnitTest;

Pcaml.inter_phrases.val := Some ";;\n" ;


module Official = struct
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
  let (implem_pa1, interf_pa1) = PAPR.both_pa1 in
  (fun name -> implem_pa1 ~{input_file=name}, fun name -> interf_pa1 ~{input_file=name})
;

value tests = "matrix" >::: (Papr_test_matrix.o2official both_pa1 Official.both_pr (Some Official.both_pa) ()) ;


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
