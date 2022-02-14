(* camlp5o *)
(* pa_llk.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;


value rewrite_str_item arg = fun [
  <:str_item:< [%llk $str:s$ ;] >> -> <:str_item< value x = 1 >>
| _ -> assert False
]
;

value install () = 
let ef = EF.mk () in 
let ef = EF.{ (ef) with
            str_item = extfun ef.str_item with [
    <:str_item:< [%llk $_$ ;] >> as z ->
    fun arg fallback ->
      Some (rewrite_str_item arg z)
  ] } in
  Pa_passthru.(install { name = "pa_llk"; ef =  ef ; pass = None ; before = [] ; after = [] })
;

install();
