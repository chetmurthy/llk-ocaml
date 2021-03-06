
[@@@llk {foo|
GRAMMAR Mod:
EXPORT: ident functor_parameter uidopt module_declaration mod_decl_binding
        sig_item;

sig_item: [ [
       "module" ; rf = V (FLAG "rec"); d = mod_decl_binding → 1
      | "module" ; i = V UIDENT "uid" ; ":="  → 2
      | "module"; "type"; i = V ident ""; "=" → 3
      | "module"; "type"; i = V ident ""; ":="  → 4
      | "module"; "alias"; i = V UIDENT "uid"; "=" → 5
      ] ] ;
  mod_decl_binding:
    [ [ i = V uidopt "uidopt"; mt = module_declaration → () ] ]
  ;
  module_declaration:
    [ [ ":" → 1
      | arg = V functor_parameter "functor_parameter" "fp" → 2
 ] ]
  ;
  functor_parameter: [ [ "("; ")" -> () ] ] ;
  uidopt: [ [ m = V UIDENT -> Some m | "_" -> None ] ] ;
  ident:
    [ [ i = LIDENT → i
      | i = UIDENT → i ] ]
  ;



END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Mod2:
EXPORT: top;

  top: [ [ s = sub1 ; ";" -> s ] ] ;
  sub1:
    [ [ u=uident1 ; ":=" → (u, true)
      | u=uident2 → (u, false) ] ]
  ;
  uident1: [ [ u = UIDENT -> u ] ] ;
  uident2: [ [ u = UIDENT -> u ] ] ;


END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Mod3:
EXPORT: top;

  top: [ [ s = sub1 ; ";" -> s ] ] ;
  sub1:
    [ [ u=uident1 ; ":=" ; l=LIDENT → (u, true, l)
      | l=lident2 ; l2 = LIDENT → (l, false, l2) ] ]
  ;
  uident1: [ [ u=UIDENT ; v = UIDENT -> (u,v) ] ] ;
  lident2: [ [ u=UIDENT ; v = LIDENT -> (u,v) ] ] ;


END ;
|foo}
] ;;

[@@@llk
{foo|
GRAMMAR Specific:
EXPORT: top;

  top: [ [ u1 ; l = LIDENT -> (1,l)
         | u = UIDENT -> (2,u)
         | u2 ; u = UIDENT -> (3,u)
         ] ] ;
  u1: [ [ UIDENT/"FOO" -> () ] ];
  u2: [ [ UIDENT/"FOO" -> () ] ];
END ;
|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "simple" >::: [
      "Mod" >:: (fun _ ->
          assert_equal "a" (pa Mod.ident "a")
        ; assert_equal () (pa Mod.functor_parameter "()")
        ; assert_equal (Some <:vala< "U" >>) (pa Mod.uidopt "U")
        ; assert_equal None (pa Mod.uidopt "_")
        ; assert_equal (Some (Ploc.VaAnt "uid:x")) (pa Mod.uidopt "$uid:x$")
        ; assert_equal 1 (pa Mod.module_declaration ":")
        ; assert_equal 2 (pa Mod.module_declaration "()")
        ; assert_equal 2 (pa Mod.module_declaration "$_fp:x$")
        ; assert_equal () (pa Mod.mod_decl_binding "_ :")
        ; assert_equal 1 (pa Mod.sig_item "module rec _ :")
        ; assert_equal 1 (pa Mod.sig_item "module X :")
        ; assert_equal 2 (pa Mod.sig_item "module X :=")
        ; assert_equal 3 (pa Mod.sig_item "module type x =")
        ; assert_equal 4 (pa Mod.sig_item "module type x :=")
        ; assert_equal 5 (pa Mod.sig_item "module alias X =")
      )
    ; "Mod2" >:: (fun _ ->
          assert_equal ("A", false) (pa Mod2.top "A;")
        ; assert_equal ("A", true) (pa Mod2.top "A := ;")
      )
    ; "Mod3" >:: (fun _ ->
          assert_equal (("A","b"), false, "c") (pa Mod3.top "A b c;")
        ; assert_equal (("A","B"), true, "d") (pa Mod3.top "A B := d;")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
