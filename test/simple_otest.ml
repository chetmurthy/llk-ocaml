open Pa_ppx_testutils
open Testutil


let lexer = Plexer.gmake ()
let g0 = Grammar.gcreate lexer ;;
[@@@llk
{foo|
GRAMMAR Extend:
EXTEND g0 ;
EXPORT: etop ;

  e[x]: [ [ f = FLAG "foo" -> (f,x) ] ] ;
  etop: [ [ x = e[1] -> x ] ] ;

END;

|foo}
] ;;


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
EXPORT: e_top e_star;
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
GRAMMAR VALA2:
EXPORT: vala1 vala2;
vala1: [ [ x = LIDENT -> <:vala< x >>
         | x = ANTI "lid" "_lid" -> x
         ] ] ;
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

  top: [ [ UIDENT/"foo" -> "foo"
         | u = UIDENT -> u
         | UIDENT/"bar" -> "bar"
         ] ] ;
END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR LocTest:
EXPORT: top;

  top: [ [ u = UIDENT ; "," ; v = UIDENT -> (loc, u,v)
         ] ] ;
END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Bug1:
EXPORT: rule;

  rule:
    [ [ psl = LIST0 psymbol SEP ";"; "->"; act = action ->
        (psl, Some act)
      | psl = LIST0 psymbol SEP ";" -> (psl, None) ] ]
  ;
  psymbol: [ [ i = LIDENT -> i ] ] ;
  action: [ [ a = UIDENT -> a ] ] ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Bug2:
EXPORT: e;

  e: [ [ x = "A" -> x ] ] ;
END;

|foo}
] ;;

type ('a, 'b) choice =
   Left of 'a
  | Right of 'b
;;

[@@@llk
{foo|
GRAMMAR Seq:
EXPORT: e;

  e:
    [
      [ "let" ; s = STRING ; "in" ; l = SELF -> (Right s) :: l
      | n = INT ; ";" ; l = SELF -> (Left n) :: l
      | n = INT ; ";" -> [ Left n ]
      | n = INT -> [ Left n ]
      ]
    ]
  ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Neg:
EXPORT: e;
REGEXPS:
  check_not_let = eps;
END ;
  e: [ [ "let" ; s = STRING -> Right ("let "^s)
       | check_not_let ; e = e1 -> e ] ] ;

  e1:
    [
      [ "let" ; s = STRING  -> Right s
      | n = INT -> Left n
      ]
    ]
  ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Empty:
EXPORT: e;

  e: [ "top"
       [ "let" ; s = STRING -> Right ("let "^s)
       | x = NEXT -> x
       ]
     | [  ]
     ] ;

  e: AFTER "top" [ [
       "value" ; n = INT -> Left (int_of_string n)
     | x = NEXT -> x
     ] ]
  ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Syntactic:
EXPORT: e;

  binder: [ [ l = LIST1 LIDENT ; "." -> l ] ] ;
  e: [
       [ (binder)? ; b = binder ; x = LIDENT -> (b, x)
       | x = LIDENT -> ([], x)
       ]
     ] ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Greedy_LIST0:
EXPORT: e;

e: [ [ h = e1 -> h ] ];
e1: [ [ "FOO" ; l1 = e2 ; l2 = LIST0 INT -> (l1, l2) ] ] ;
e2: [ [ l = GREEDY LIST0 INT -> l ] ] ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Greedy_LIST1:
EXPORT: e;

e: [ [ h = e1 -> h ] ];
e1: [ [ "FOO" ; l1 = e2 ; l2 = LIST0 INT -> (l1, l2) ] ] ;
e2: [ [ l = GREEDY LIST1 INT -> l ] ] ;
END;

|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Greedy_LIST1_SEP:
EXPORT: e;

e: [ [ h = e1 -> h ] ];
e1: [ [ "FOO" ; l1 = e2 ; l2 = LIST0 INT -> (l1, l2) ] ] ;
e2: [ [ l = GREEDY LIST1 INT SEP "," -> l ] ] ;
END;

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
    ; "LocTest" >:: (fun _ ->
      let loc = Ploc.make_loc "" 1 0 (0, 4) "" in
        assert_equal ~cmp:(fun (_,a1,b1) (_,a2,b2) -> a1=a2 && b1=b2) (loc, "U","V") (pa LocTest.top {|U, V|})
    )
    ; "Seq" >:: (fun _ ->
        assert_equal [Left "0"] (pa Seq.e {|0|})
      ; assert_equal [Left "0"] (pa Seq.e {|0 ;|})
      ; assert_equal [Left "0"; Left "1"] (pa Seq.e {|0 ; 1 ;|})
      ; assert_equal [Right "foo" ; Left "0"; Left "1"] (pa Seq.e {|let "foo" in 0 ; 1 ;|})
      ; assert_equal [Left "2" ; Right "foo" ; Left "0"; Left "1"] (pa Seq.e {|2 ; let "foo" in 0 ; 1 ;|})
    )
    ; "Neg" >:: (fun _ ->
        assert_equal (Right "let a") (pa Neg.e {|let "a"|})
      ; assert_equal (Left "0") (pa Neg.e {|0|})
    )
    ; "Empty" >:: (fun _ ->
        assert_equal (Right "let a") (pa Empty.e {|let "a"|})
      ; assert_equal (Left 0) (pa Empty.e {|value 0|})
    )
    ; "Syntactic" >:: (fun _ ->
        assert_equal ([], "x") (pa Syntactic.e {|x|})
      ; assert_equal (["x"; "y"], "z") (pa Syntactic.e {|x y.z|})
    )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
