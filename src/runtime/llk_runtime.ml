open Pa_ppx_utils ;

value parse_flag pfun = parser [
  [: _ = pfun :] -> True
| [: :] -> False
]
;

value parse_opt pfun = parser [
  [: x = pfun :] -> Some x
| [: :] -> None
]
;

(*
value parse_left_assoc lhs restrhs combiner = parser [
  [: x = lhs ; rv = parser [ [: y = restrhs :] -> combiner x y | [: :] -> x ] :] -> rv 
]
;
 *)
value parse_left_assoc lhs restrhs combiner =
  let rec pleft x = parser [
    [: y = restrhs ; strm :] -> pleft (combiner x y) strm
  | [: :] -> x
  ] in
  parser [
   [: x = lhs ; rv = pleft x :] -> rv
  ]
;

value parse_list0 elem =
  let rec prec = parser [
    [: e = elem ; strm :] -> [e :: prec strm]
  | [: :] -> []
  ]
  in prec
;

value parse_list1 elem = parser [
    [: e = elem ; strm :] -> [e :: parse_list0 elem strm]
]
;

value parse_list1_with_sep elem sep =
  let rec prec = parser [
    [: e = elem ; _ = sep ; strm :] -> [e :: prec strm]
  | [: e = elem :] -> [e]
  ]
  in prec
;

value parse_list0_with_sep elem sep = parser [
  [: e = elem ; _ = sep ; l = parse_list1_with_sep elem sep :] -> [e :: l]
| [: e = elem :] -> [e]
| [: :] -> []
]
;

value parse_list0_with_sep_opt_trailing elem sep =
  let rec prec = parser [
    [: e = elem ; _ = sep ; strm :] -> [e :: prec strm]
  | [: e = elem :] -> [e]
  | [: :] -> []
  ]
  in prec
;

value parse_list1_with_sep_opt_trailing elem sep = parser [
  [: e = elem ; _ = sep ; l = parse_list0_with_sep_opt_trailing elem sep :] -> [e :: l]
| [: e = elem ; _ = sep :] -> [e]
| [: e = elem :] -> [e]
]
;

value parse_antiquot elem kinds = parser [
  [: `("ANTIQUOT", x) when
      match Plexer.parse_antiquot x with [
          Some (k, _) -> List.mem k kinds
        | _ -> False
        ] :] -> Ploc.VaAnt x
| [: v = elem :] -> Ploc.VaVal v
]
;

value parse_antiquot_token kinds = parser [
  [: `("ANTIQUOT", x) when
      match Plexer.parse_antiquot x with [
          Some (k, _) -> List.mem k kinds
        | _ -> False
        ] :] -> Ploc.VaAnt x
]
;

value must_peek_nth n strm : option (string * string) =
  let l = Stream.npeek n strm in
  if List.length l = n then Some (fst (Asttools.sep_last l))
  else None
;

value clone_stream strm =
  let rec crec n =
    match must_peek_nth n strm with [
        Some tok -> [: `tok ; crec (n+1) :]
      | None -> [: :]
      ]
  in [: crec 1 :]
;

value must_parse ~{msg} pa strm =
  try pa strm
  with [
      Stream.Failure ->
      let open Printexc in
       let rbt = get_raw_backtrace() in
      raise_with_backtrace (Stream.Error msg) rbt
    ]
;
