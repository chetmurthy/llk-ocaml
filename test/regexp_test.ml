
[%llk
{foo|
GRAMMAR Longident:
GLOBAL: longident longident_eoi;

REGEXPS:
  check_dot_uid = "." (UIDENT | $uid | $_uid) ;
END;
  longident:
    [ LEFTA
      [ me1 = SELF; (* check_dot_uid ;*) "."; i = V UIDENT "uid" -> me1 @ [i] ]
    | [ i = V UIDENT "uid" -> [i] ]
    ]
  ;
  longident_eoi: [ [ x = longident ; EOI -> x ] ] ;
END ;
|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "simple" >::: [
      "LLK" >:: (fun _ ->
          assert_equal [<:vala< "A" >>; <:vala< "B" >>; <:vala< "C" >>] (pa Longident.longident_eoi "A.B.C")
        ; assert_equal [<:vala< "A" >>] (pa Longident.longident_eoi "A")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
