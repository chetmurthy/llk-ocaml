
[@@@llk
{foo|
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
EXPORT: type_binder_opt ctyp sig_item sig_item_eoi ;

  ident:
    [ [ i = LIDENT → i
      | i = UIDENT → i ] ]
  ;
  typevar:
    [ [ "'"; i = ident → i 
      | i = GIDENT -> i
      ] ]
  ;
  type_binder_opt: [ [
    ls = V (LIST1 typevar) ; "." -> ls
  | -> <:vala< [] >>
  ] ]
  ;

  sig_item:
    [ "top"
      [ "external"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp →
          1
      ] ]
      ;
  sig_item_eoi: [ [ x = sig_item ; EOI -> x ] ] ;

  ctyp:
    [ "simple"
      [ LIST0 typevar ; OPT LIDENT -> 1
      ]
    ]
    ;

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
          assert_equal 1 (pa Mod2.sig_item_eoi "external a : 'a")
        ; assert_equal 1 (pa Mod2.sig_item_eoi "external a : 'a 'b . 'a")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
