
[%llk
{foo|
GRAMMAR LLK:
GLOBAL: str_item;
(*
REGEXPS:

  tyvar = "'" (LIDENT | UIDENT) | GIDENT ;
  type_parameter = ("+"|"-"|"!"|"!+"|"+!"| "!-"|"-!")* (tyvar | "_") ;
  type_parameters = ("$list" | "$_list" | type_parameter* ) ;
  check_type_decl = ("$flag" | "$_flag" |
          ("rec"|"nonrec") |
          ("$list" | "$_list") |
          (LIDENT | "$tp" | "$_tp" | "$lid" | "$_lid") type_parameters ("=" | ":=")) ;
  check_type_extension = UIDENT | "$lilongid" | "$_lilongid" | (LIDENT type_parameters "+=") ;
END ;
*)
str_item: [ [ x = LIDENT -> x ] ] ;

(*
str_item:
    [ [
        "type"; check_type_decl ; nrfl = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") → do {
          vala_it (fun tdl ->
            if List.exists (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl then
              failwith "type-declaration cannot mix decl and subst"
            else ()) tdl ;
            <:str_item< type $_flag:nrfl$ $_list:tdl$ >>
          }
      | "type" ; check_type_extension ; te = type_extension →
          <:str_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >>
      ] ] ;
*)
END;

|foo}
] ;;

let pa e s = s |> Stream.of_string |> Grammar.Entry.parse e

open OUnit2
open OUnitTest
let tests = "simple" >::: [
      "LLK" >:: (fun _ ->
        ()
      )
]


if not !Sys.interactive then
  run_test_tt_main tests ;;
  
(*
;;; Local Variables: ***
;;; mode:tuareg ***
;;; End: ***

*)
