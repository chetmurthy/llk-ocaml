
open Pcaml ;;

[@@@llk
{foo|
GRAMMAR Mod:
EXPORT: expr1;

REGEXPS:
  check_uident_coloneq = (UIDENT | $uid | $_uid) ":=" ;
  check_module_decl_binding = "rec"? ( UIDENT | "_" | $_uidopt | $uidopt) (":" | "(") ;
END;

external expr : PREDICTION LIDENT ;

expr1 : [ [ e = expr -> e ] ] ;

END ;
|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let loc = Ploc.dummy
let tests = "simple" >::: [
      "Mod" >:: (fun _ ->
          assert_equal ~cmp:Reloc.eq_expr <:expr< a >> (pa Mod.expr1 "a")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
