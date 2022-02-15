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

[%llk
{foo|
GRAMMAR I:
GLOBAL: e;
  elist[(l:(int * bool) list)]:
    [ [
        n = INT ; ";" ; rv=elist[((int_of_string n,true)::l)] -> rv
      | n = INT ; ";" ; b = bool ; ";" ; rv=elist[((int_of_string n,b)::l)] -> rv
      | -> l ] ]
  ;
  bool: [ [ "true" -> true | "false" -> false ] ] ;
  e: [ [ l = elist[[]] -> List.rev l ] ] ;
END;

|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "flag1" >::: [
      "G" >:: (fun _ ->
        assert_equal (true, 1) (pa G.etop "foo")
      )
    ; "H" >:: (fun _ ->
      assert_equal (1, (true, 3)) (pa H.etop "foo 3")
    )
    ; "I" >:: (fun _ ->
        assert_equal [] (pa I.e "")
      ; assert_equal [(1,true)] (pa I.e "1;")
      ; assert_equal [(1,false);(2,true)] (pa I.e "1;false;2;")
    )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
