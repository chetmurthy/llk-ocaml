
[@@@llk
{foo|
GRAMMAR Mod:
EXPORT: ident functor_parameter uidopt module_declaration mod_decl_binding
        sig_item;

REGEXPS:
  check_uident_coloneq = (UIDENT | $uid | $_uid) ":=" ;
  check_module_decl_binding = "rec"? ( UIDENT | "_" | $_uidopt | $uidopt) (":" | "(") ;
END;
sig_item: [ [
       "module" ; check_module_decl_binding ; rf = V (FLAG "rec"); d = mod_decl_binding → 1
      | "module" ; check_uident_coloneq ; i = V UIDENT "uid" ; ":="  → 2
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
GRAMMAR Types:
EXPORT: type_binder_opt ctyp sig_item ;
REGEXPS:
  check_type_binder = 
        let tyvar = "'" (LIDENT | UIDENT) | GIDENT in
         (tyvar tyvar * | ($list | $_list)) "." ;
END;

(*
  infix_operator0: [ [
      x = INFIXOP0 -> x
    | "!=" -> "!="
    | "<>" -> "<>"
    | "=" -> "="
    | "<" -> "<"
    | ">" -> ">"
    | "||" -> "||"
    | "or" -> "or"
    | "&" -> "&"
    | "&&" -> "&&"
(* NOTE WELL: "$" is not a supported operator in Camlp5's revised syntax,
   b/c conflicts with antiquotations, e.g. <:expr< a $ $lid:id$ >> would
   *suck* to parse
    | "$" -> "$"
 *)
    ] ]
    ;
  infix_operator1: [ [
      x = INFIXOP1 -> x
    | "@" -> "@"
    | "^" -> "^"
    ] ]
    ;
  additive_operator2: [ [
      "+" -> "+"
    | "+=" -> "+="
    | "-" -> "-"
    | "+." -> "+."
    | "-." -> "-."
    ] ]
    ;
  infix_operator2: [ [
      x = INFIXOP2 -> x
    | x = additive_operator2 -> x
    ] ]
    ;
  infix_operator3: [ [
      x = INFIXOP3 -> x
    | "lor" -> "lor"
    | "lxor" -> "lxor"
    | "mod" -> "mod"
    | "land" -> "land"
    | "*" -> "*"
    | "/" -> "/"
    | "%" -> "%"
    ] ]
    ;
  infix_operator4: [ [
      x = INFIXOP4 -> x
    | "asr" -> "asr"
    | "lsl" -> "lsl"
    | "lsr" -> "lsr"
    | "**" -> "**"
    ] ]
    ;
  prefix_operator: [ [
      x = PREFIXOP -> x
    | "!" -> "!"
    ] ]
    ;
  infix_operator: [ [ 
      x = infix_operator0 -> x
    | x = infix_operator1 -> x
    | x = infix_operator2 -> x
    | x = infix_operator3 -> x
    | x = infix_operator4 -> x
    | ":=" -> ":="
    ] ]
    ;
  operator: [ [
      x = prefix_operator -> x
    | x = infix_operator -> x
    | x = HASHOP -> x
    | op = LETOP -> op
    | op = ANDOP -> op
    | op = "::" -> op

    | op = DOTOP ; "(" ; ")" -> op ^ "()"
    | op = DOTOP ; "(" ; ")" ; "<-" -> op ^ "()<-"
    | op = DOTOP ; "(" ; ";" ; ".." ; ")" -> op ^ "(;..)"
    | op = DOTOP ; "(" ; ";" ; ".." ; ")" ; "<-" -> op ^ "(;..)<-"

    | op = DOTOP ; "{" ; "}" -> op ^ "{}"
    | op = DOTOP ; "{" ; "}" ; "<-" -> op ^ "{}<-"
    | op = DOTOP ; "{" ; ";" ; ".." ; "}" -> op ^ "{;..}"
    | op = DOTOP ; "{" ; ";" ; ".." ; "}" ; "<-" -> op ^ "{;..}<-"

    | op = DOTOP ; "[" ; "]" -> op ^ "[]"
    | op = DOTOP ; "[" ; "]" ; "<-" -> op ^ "[]<-"
    | op = DOTOP ; "[" ; ";" ; ".." ; "]" -> op ^ "[;..]"
    | op = DOTOP ; "[" ; ";" ; ".." ; "]" ; "<-" -> op ^ "[;..]<-"
    ] ]
    ;
  operator_rparen: [ [
      op = operator ; ")" -> op
    ] ]
    ;
*)
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
    check_type_binder ; ls = V (LIST1 typevar) ; "." -> ls
  | -> <:vala< [] >>
  ] ]
  ;

  sig_item:
    [ "top"
      [ "external"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp →
          1
(*
      | "external"; "("; i = operator_rparen; ":"; ls = type_binder_opt ; t = ctyp →
          2
*)
      ] ]
      ;

  ctyp:
    [ "simple"
      [ "'"; i = V ident "" → 1
      | i = GIDENT → 2
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
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
