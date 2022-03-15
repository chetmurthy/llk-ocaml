open Pa_ppx_testutils
open Testutil

[@@@llk
{foo|
GRAMMAR G:
EXPORT: etop ;

  e[x]: [ [ f = FLAG "foo" -> (f,x) ] ] ;
  etop: [ [ x = e[1] -> x ] ] ;

END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR H:
EXPORT: etop;
  e[x]: [ [ y = FLAG "foo" ; z = f[y] -> (x,z) ] ] ;
  f[x]: [ [ z = INT -> (x,int_of_string z) ] ] ;
  etop: [ [ l = e[1] -> l ] ] ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR I:
EXPORT: e;
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

[@@@llk
{foo|
GRAMMAR Calc:
EXPORT: e_top;
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

[@@@llk
{foo|
GRAMMAR Lists:
EXPORT: id list0 list1 list0sep list1sep list0sep_opt list1sep_opt;
list0: [ [ l = LIST0 id -> l ] ] ;
list1: [ [ l = LIST1 id -> l ] ] ;
list0sep: [ [ l = LIST0 id SEP "," -> l ] ] ;
list1sep: [ [ l = LIST1 id SEP "," -> l ] ] ;
list0sep_opt: [ [ l = LIST0 id SEP "," OPT_SEP -> l ] ] ;
list1sep_opt: [ [ l = LIST1 id SEP "," OPT_SEP -> l ] ] ;
id: [ [ id = LIDENT -> id | id = UIDENT -> id ] ] ;
END;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR VALA:
EXPORT: vala1 vala2;
vala1: [ [ x = V LIDENT -> x ] ] ;
vala2: [ [ x = V LIDENT "a" "b" -> x ] ] ;
END;
|foo}
] ;;


[@@@llk
{foo|
GRAMMAR Longident:
EXPORT: longident longident_eoi;

  longident:
    [ LEFTA
      [ me1 = SELF; "."; i = V UIDENT "uid" -> me1 @ [i] ]
    | [ i = V UIDENT "uid" -> [i] ]
    ]
  ;
  longident_eoi: [ [ x = longident ; EOI -> x ] ] ;
END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR VUID:
EXPORT: uidopt;

  uidopt: [ [ m = V UIDENT -> Some m | "_" -> None ] ] ;
END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR LF:
EXPORT: top;

  a: [ [ x = INT -> int_of_string x ] ];
  b: [ [ x = FLOAT -> float_of_string x ] ];
  c: [ [ x = STRING -> x ] ];
  d: [ [ x = UIDENT -> x ] ];
  e: [ [ x = LIDENT -> x ] ];

  top: [ [ x = a ; y = b ; z = c; w = e -> (x,y,z,w)
         | x = a ; y = b ; z = c; w = d -> (x,y,z,w)
         ] ] ;
END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR LLift:
EXPORT: top;

  a: [ [ x = INT -> int_of_string x ] ];
  b: [ [ x = FLOAT -> float_of_string x ] ];
  c: [ [ x = STRING -> x ] ];
  d: [ [ x = UIDENT -> x ] ];
  e: [ [ x = LIDENT -> x ] ];

  top: [ [ x = a ; y = b ;
           (z2,w2) = [ z = c; w = e -> (z,w)
                   | z = c; w = d -> (z,w)
                   ] -> (x,y,z2,w2)
         ] ] ;
END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Specific:
EXPORT: top;

  top: [ [ UIDENT "foo" -> "foo"
         | u = UIDENT -> u
         | UIDENT "bar" -> "bar"
         ] ] ;
END ;
|foo}
] ;;

let matches ~pattern text =
  match Str.search_forward (Str.regexp pattern) text 0 with
    _ -> true
  | exception Not_found -> false
;;

let assert_raises_exn_pattern pattern f =
  Testutil.assert_raises_exn_pred
    (fun e ->
      let s = Printexc.to_string e in
      matches ~pattern s)
    f
;;

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
    ; "Lists:list0" >:: (fun _ ->
        assert_equal "x" (pa Lists.id "x")
      ; assert_equal "X" (pa Lists.id "X")
      ; assert_equal [] (pa Lists.list0 "")
      ; assert_equal ["x"] (pa Lists.list0 "x")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list0 "x Y z")
    )
    ; "Lists:list1" >:: (fun _ ->
        assert_raises_exn_pattern "illegal begin of list1" (fun () -> pa Lists.list1 "")
      ; assert_equal ["x"] (pa Lists.list1 "x")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list1 "x Y z")
    )
    ; "Lists:list0sep" >:: (fun _ ->
        assert_equal [] (pa Lists.list0sep "")
      ; assert_equal ["x"] (pa Lists.list0sep "x")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list0sep "x,Y,z")
    )
    ; "Lists:list1sep" >:: (fun _ ->
        assert_raises_exn_pattern "illegal begin of list1" (fun () -> pa Lists.list1sep "")
      ; assert_equal ["x"] (pa Lists.list1sep "x")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list1sep "x,Y,z")
    )
    ; "Lists:list0sep_opt" >:: (fun _ ->
        assert_equal [] (pa Lists.list0sep_opt "")
      ; assert_equal ["x"] (pa Lists.list0sep_opt "x")
      ; assert_equal ["x"] (pa Lists.list0sep_opt "x,")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list0sep_opt "x,Y,z")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list0sep_opt "x,Y,z,")
    )
    ; "Lists:list1sep_opt" >:: (fun _ ->
        assert_raises_exn_pattern "illegal begin of list1" (fun () -> pa Lists.list1sep_opt "")
      ; assert_equal ["x"] (pa Lists.list1sep_opt "x")
      ; assert_equal ["x"] (pa Lists.list1sep_opt "x,")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list1sep_opt "x,Y,z")
      ; assert_equal ["x";"Y";"z"] (pa Lists.list1sep_opt "x,Y,z,")
    )
    ; "VALA" >:: (fun _ ->
        assert_equal (Ploc.VaVal "x") (pa VALA.vala1 "x")
      ; assert_equal (Ploc.VaAnt "lid:x") (pa VALA.vala1 "$lid:x$")
      ; assert_equal (Ploc.VaVal "x") (pa VALA.vala2 "x")
      ; assert_equal (Ploc.VaAnt "a:x") (pa VALA.vala2 "$a:x$")
      ; assert_equal (Ploc.VaAnt "b:x") (pa VALA.vala2 "$b:x$")
    )
    ; "Longident" >:: (fun _ ->
          assert_equal [<:vala< "A" >>; <:vala< "B" >>; <:vala< "C" >>] (pa Longident.longident_eoi "A.B.C")
        ; assert_equal [<:vala< "A" >>] (pa Longident.longident_eoi "A")
      )
    ; "VUID" >:: (fun _ ->
        assert_equal None (pa VUID.uidopt "_")
      ; assert_equal (Some <:vala< "U" >>) (pa VUID.uidopt "U")
      ; assert_equal (Ploc.VaAnt "lid:x") (pa VALA.vala1 "$lid:x$")
    )
    ; "LF" >:: (fun _ ->
        assert_equal (1, 2., "c", "X") (pa LF.top {|1 2. "c" X|})
      ; assert_equal (1, 2., "c", "y") (pa LF.top {|1 2. "c" y|})
    )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
