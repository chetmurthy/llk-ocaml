[@@@llk
{foo|
GRAMMAR Revised:
  EXPORT: sig_item str_item ctyp module_type
    signature
    with_constr
    ;

  str_item:
    [ "top"
      [ "module"; "type"; i = V LIDENT "";  "="; mt = module_type →
          <:str_item< module type $_:i$ = $mt$ >>
      ] ]
  ;

  module_type:
    [ "->" RIGHTA [ mt1=SELF ; "->" ; mt2=SELF ->
         <:module_type< $mt1$ → $mt2$ >>
       ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; "]" ->
        <:module_type< $e1$ [@foo (); ] >>
      ]
    | LEFTA [ mt = SELF; "with"; wc = with_constr →
          <:module_type< $mt$ with $list:[wc]$ >> ]
    | [ "sig"; sg = signature; "end" →
          <:module_type< sig $_list:sg$ end >> ]
    | "simple"
      [ i = V LIDENT → <:module_type< $_lid:i$ >>
      | "("; mt = SELF; ")" → <:module_type< $mt$ >> ] ]
  ;
  signature:
    [ [ st = V (LIST0 [ s = sig_item; ";" → s ]) → st ] ]
  ;
  sig_item:
    [ "top"
      [ "module"; "type"; i = V LIDENT ""; "="; mt = module_type →
          <:sig_item< module type $_:i$ = $mt$ >>
      ] ]
  ;
  with_constr:
    [ [ "type"; i = LIDENT;
        "="; pf = V (FLAG "private"); t = ctyp_below_alg_attribute →
          <:with_constr< type $lid:i$ = $_flag:pf$ $t$ >>
      ] ]
  ;

  ctyp:
    [ "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; "]" ->
        <:ctyp< $e1$ [@foo (); ] >>
      ]
    | "below_alg_attribute" [ t = NEXT -> t ]
    | "arrow" NONA
      [ t1 = NEXT ; PRIORITY 1 ; "->"; t2 = SELF → <:ctyp< $t1$ → $t2$ >>
      | t1 = NEXT -> t1
      ]
    | "simple"
      [ i = LIDENT → <:ctyp< $lid:i$ >>
      | "("; t = SELF; ")" → <:ctyp< $t$ >>
 ] ]
  ;
  ctyp_below_alg_attribute:
  [ [ x = ctyp LEVEL "below_alg_attribute" -> x ]
  ]
  ;

END ;
|foo} ;
];
