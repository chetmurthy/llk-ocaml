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

[%llk
{foo|
GRAMMAR Calc:
GLOBAL: e_top;
  e_top: [ [ x = e -> x ] ] ;

  e_star: [ [ x = e LEVEL "*" -> x ] ] ;

  e: AFTER "**"
    [ NONA [ x = FLOAT -> float_of_string x
      | "("; x = e; ")" -> x ] ]
  ;

  e: BEFORE "*"
    [ LEFTA [ x1 = e; "+"; y = e -> x1 +. y
      | x2 = e; "-"; y = e -> x2 -. y ]
    ]
  ;

  e: AFTER "*"
    [ "**" RIGHTA [ x = e; "**"; y = e -> Float.pow x  y ]
    ]
  ;

  e:
    [ "*" LEFTA [ x = e; "*"; y = e -> x *. y
      | x = e; "/"; y = e -> x /. y ] ]
  ;

END;

|foo}
] ;;

[%llk
{foo|
GRAMMAR Re1:
GLOBAL: e_top;
REGEXPS: foo = "a" ; bar = "b" ; END ;
  e_top: [ [ x = LIDENT -> x ] ] ;

END;

|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "simple" >::: [
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
    ; "Calc" >:: (fun _ ->
        assert_equal 5. (pa Calc.e_top "5.")
      ; assert_equal 25. (pa Calc.e_top "5. ** 2.")
      ; assert_equal 50. (pa Calc.e_top "5. ** 2. * 2.")
      ; assert_equal 51. (pa Calc.e_top "5. ** 2. * 2. + 1.")
    )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
