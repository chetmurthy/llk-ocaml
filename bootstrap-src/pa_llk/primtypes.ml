
module Name = struct
  type t = (string * int)[@@deriving (show,eq,ord) ;] ;
  value mk s = (s, -1) ;
  value fresh (s, _) n = (s, n) ;
  value print = fun [
    (s,-1) -> s
  | (s,n) -> Fmt.(str "%s__%04d" s n)
  ]
  ;
  value pp pps n = Fmt.(pf pps "%s" (print n)) ;
  value root (s, _) = s ;
end
;
