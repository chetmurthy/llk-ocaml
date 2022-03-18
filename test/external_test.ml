
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

expr1 : [ [ e = expr -> Some e | -> None ] ] ;

END ;
|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

type expr = MLast.expr
type patt = MLast.patt
let equal_expr = Reloc.eq_expr
let equal_patt = Reloc.eq_patt
type expr_option = expr option [@@deriving eq]

open OUnit2
open OUnitTest
let loc = Ploc.dummy
let tests = "simple" >::: [
      "Mod" >:: (fun _ ->
          assert_equal ~cmp:equal_expr_option (Some <:expr< a >>) (pa Mod.expr1 "a")
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
