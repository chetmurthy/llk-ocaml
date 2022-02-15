[%llk
{foo|
GRAMMAR G:
GLOBAL: etop ;

  e[x]: [ [ f = FLAG "foo" -> (f,x) ] ] ;
  etop: [ [ x = e[1] -> x ] ] ;

END;

|foo}
]

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "flag1" >::: [
  "simplest" >:: (fun _ ->
        assert_equal (true, 1) (pa G.etop "foo")
  )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
