
[%llk
{foo|
GRAMMAR Re1:
GLOBAL: top;

REGEXPS: foo = "a" ; bar = "b" ; END ;
  top:
  [ [
      l = LIST1 LIDENT ; u = UIDENT ; "=" -> (l,u)
  ] ] ;

END;

|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "simple" >::: [
      "G" >:: (fun _ ->
        assert_equal ~msg:"not equal" (["x"],"U") (pa Re1.top "x U =")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
