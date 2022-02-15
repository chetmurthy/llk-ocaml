[%llk
{foo|
GRAMMAR G:
GLOBAL: etop ;

  e[x]: [ [ f = FLAG "foo" -> (f,x) ] ] ;
  etop: [ [ x = e[1] -> x ] ] ;

END;

|foo}
] ;;

[%llk
{foo|
GRAMMAR H:
GLOBAL: etop;
  e[x]: [ [ y = FLAG "foo" ; z = f[y] -> (x,z) ] ] ;
  f[x]: [ [ z = INT -> (x,int_of_string z) ] ] ;
  etop: [ [ l = e[1] -> l ] ] ;
END;

|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "flag1" >::: [
      "1" >:: (fun _ ->
        assert_equal (true, 1) (pa G.etop "foo")
      )
(*
    ; "2" >:: (fun _ ->
        assert_equal (true, 1) (pa H.etop "foo")
  )
 *)
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
