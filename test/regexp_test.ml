
[%llk
{foo|
GRAMMAR Mod:
GLOBAL: ident functor_parameter uidopt
        sig_item;

REGEXPS:
  check_uident_coloneq = (UIDENT | $uid | $_uid) ":=" ;
  check_module_decl_binding = "rec"? ( UIDENT | "_" | $_uidopt | $uidopt) (":" | "(") ;
END;
sig_item: [ [
       "module"; check_module_decl_binding ; rf = V (FLAG "rec"); d = mod_decl_binding → 1
      | "module"; check_uident_coloneq ; i = V UIDENT "uid" ; ":="  → 2
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

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "simple" >::: [
      "Mod" >:: (fun _ ->
          assert_equal "a" (pa Mod.ident "a")
        ; assert_equal () (pa Mod.functor_parameter "()")
        ; assert_equal (Some <:vala< "U" >>) (pa Mod.uidopt "U")
        ; assert_equal (Some <:vala< "U" >>) (pa Mod.uidopt "$uid:x$")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
