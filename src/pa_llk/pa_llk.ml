(* camlp5o *)
(* pa_llk.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Pa_ppx_base ;
open Pa_passthru ;
open Ppxutil ;

open Comp_llk ;

value codegen loc ~{bootstrap} s =
  try
    Top.codegen ~{bootstrap=bootstrap} s
  with [ Ploc.Exc loc' exn ->
         let rbt = Printexc.get_raw_backtrace () in
         let loc' = Ploc.(make_loc
                            (file_name loc)
                            (line_nb loc + line_nb loc')
                            (bol_pos loc')
                            (first_pos loc', last_pos loc')
                            (comment loc')) in
         Printexc.raise_with_backtrace (Ploc.Exc loc' exn) rbt
       ]
;

value rewrite_str_item arg = fun [
  <:str_item:< [@@@llk.fallback $str:s$ ;] >> ->
  codegen loc ~{bootstrap=False} (Scanf.unescaped s)
| <:str_item:< [@@@llk $str:s$ ;] >> ->
  codegen loc ~{bootstrap=True} (Scanf.unescaped s)
| _ -> assert False
]
;

value install () = 
let ef = EF.mk () in 
let ef = EF.{ (ef) with
            str_item = extfun ef.str_item with [
    (<:str_item:< [@@@llk.fallback $_$ ;] >> | <:str_item:< [@@@llk $_$ ;] >>) as z ->
    fun arg fallback ->
      Some (rewrite_str_item arg z)
  ] } in
  Pa_passthru.(install { name = "pa_llk"; ef =  ef ; pass = None ; before = [] ; after = [] })
;

install();
