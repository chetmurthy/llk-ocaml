(* camlp5o *)
(* pa_llk.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;

open Comp_llk ;

value rewrite_str_item arg = fun [
  <:str_item:< [@@@llk $str:s$ ;] >> ->
  Top.codegen (Scanf.unescaped s)
| <:str_item:< [@@@llk.bootstrapped $str:s$ ;] >> ->
  Top.codegen ~{bootstrap=True} (Scanf.unescaped s)
  
| _ -> assert False
]
;

value install () = 
let ef = EF.mk () in 
let ef = EF.{ (ef) with
            str_item = extfun ef.str_item with [
    (<:str_item:< [@@@llk $_$ ;] >> | <:str_item:< [@@@llk.bootstrapped $_$ ;] >>) as z ->
    fun arg fallback ->
      Some (rewrite_str_item arg z)
  ] } in
  Pa_passthru.(install { name = "pa_llk"; ef =  ef ; pass = None ; before = [] ; after = [] })
;

install();
