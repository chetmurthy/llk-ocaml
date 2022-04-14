open Pa_ppx_base ;
open Ppxutil ;

module Name = struct
  open Pcre ;
  value name_rex = regexp "^(.*?)(?:__([0-9]{4}))?$" ;
  value decompose s =
    let ss = exec ~{rex=name_rex} s in
    match get_substrings ss with [
      [|_;root;""|] -> (root, -1)
    | [|_;root;num|] -> (root, int_of_string num)
    | _ -> Fmt.(failwithf "Name.decompose: internal error: name %a was not decomposable" Dump.string s)
    ]
  ;

  type t = (string * int)[@@deriving (show,eq,ord) ;] ;
  value mk0 s n = (s, n) ;
  value mk s = decompose s ;
  value fresh (s, _) n = (s, n) ;
  value print = fun [
    (s,-1) -> s
  | (s,n) -> Fmt.(str "%s__%04d" s n)
  ]
  ;
  value pp pps n = Fmt.(pf pps "%s" (print n)) ;
  value root (s, _) = s ;
  value is_generated (_, n) = n > -1 ;

end
;
