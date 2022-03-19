(* camlp5r *)
(* token_regexps.ml,v *)

open Asttools ;
open Brzozowski2 ;
open Pa_ppx_base ;
open Pp_MLast ;
open Pa_ppx_utils ;
open Ppxutil ;

module PatternBaseToken = struct
  value lident_re = Str.regexp "^[a-z_][a-zA-Z0-9_]*$" ;
  value is_lident s = Str.string_match lident_re s 0 ;

  type t = [ CLS of string and option string | SPCL of string | ANTI of string | OUTPUT of int ] ;
  value hash = Hashtbl.hash;
  value print = fun [
      SPCL s -> Printf.sprintf "\"%s\"" (String.escaped s)
    | CLS ty None -> Printf.sprintf "%s" ty
    | CLS ty (Some s) -> Printf.sprintf "%s \"%s\"" ty (String.escaped s)
    | ANTI s when is_lident s -> Printf.sprintf "$%s" s
    | ANTI s  -> Printf.sprintf "$\"%s\"" (String.escaped s)
    | OUTPUT n -> Printf.sprintf "#%d" n
    ]
  ;
  value compare t1 t2 = Stdlib.compare t1 t2 ;                            
  value equal t1 t2 = 0 = compare t1 t2 ;
  value is_output = fun [ OUTPUT _ -> True | _ -> False ] ;

end ;
module PatternRegexp = Regexp(PatternBaseToken) ;
module PSyn = RESyntax(PatternBaseToken)(PatternRegexp) ;

module Compile(R : sig value rex : PatternRegexp.regexp ;
                       value extra : list PatternBaseToken.t ;
                   end) = struct
  open PatternBaseToken ;
  value toks = (PatternRegexp.tokens R.rex @ R.extra)
               |> List.sort_uniq compare ;
  module PatternToken = struct
    include PatternBaseToken ;
    value foreach f = do {
      List.iter f toks ;
      f (CLS "EOI" None)
    }
    ;
  end ;
  module BEval = Eval(PatternToken)(PatternRegexp) ;
  value dfa = BEval.Dfa.dfa R.rex ;
  value exec input = BEval.Dfa.exec dfa input ;
end
;

value compile rex =
  let module C = Compile(struct value rex = rex ; value extra = [] ; end) in
  C.exec
;

value convert_token =
  let open PatternBaseToken in
  fun [
      ("",s) -> Some (SPCL s)
    | ("ANTIQUOT", s) -> s |> Plexer.parse_antiquot |> option_map fst |> option_map (fun s -> ANTI s)
    | ("ANTIQUOT_LOC", s) -> s |> Plexer.parse_antiloc |> option_map snd3 |> option_map (fun s -> ANTI s)
    | (s, _) -> Some (CLS s None)
]
;

value nondestructive_token_stream_to_string_seq ~{convert} strm =
  let rec trec ofs () =
    let l = Stream.npeek ofs strm in
    if List.length l = ofs then
      let tok = fst (sep_last l) in
      match convert tok with [
          None -> Seq.Nil
        | Some s -> Seq.Cons s (trec (ofs+1))
        ]
    else Seq.Nil
  in trec 1
;

value check_regexp ?{convert=convert_token} rex =
  let e = compile rex in
  fun strm ->
  match e (nondestructive_token_stream_to_string_seq ~{convert=convert} strm) with [
    None -> False
  | Some _ -> True
  ]
;

value concatenation l =
  List.fold_left PSyn.(fun e1 e2 -> e1 @@ e2) (List.hd l) (List.tl l)
;

type loc = Ploc.t ;
value compare_loc a b = 0 ;
value equal_loc a b = True ;

type astre = [
  Special of loc and string
| Class of loc and string and option string
| Anti of loc and string
| Output of loc and int
| DISJ of loc and list astre
| CONJ of loc and list astre
| CONC of loc and list astre
| STAR of loc and astre
| NEG of loc and astre
| OPT of loc and astre
| EPS of loc
| LETIN of loc and string and astre and astre
| ID of loc and string
] [@@deriving (show,eq,ord) ;]
;

value normalize_astre env x =
  let open PatternBaseToken in
  let rec convrec env = fun [
        Special _ x -> PSyn.token (SPCL (Scanf.unescaped x))
      | Class _ x None -> PSyn.token (CLS (Scanf.unescaped x) None)
      | Class _ x (Some s) -> PSyn.token (CLS (Scanf.unescaped x) (Some (Scanf.unescaped s)))
      | Anti _ x -> PSyn.token (ANTI (Scanf.unescaped x))
      | Output _ x -> PSyn.token (OUTPUT x)
      | DISJ _ l -> PSyn.disjunction (List.map (convrec env) l)
      | CONJ _ l -> PSyn.conjunction (List.map (convrec env) l)
      | CONC _ l -> concatenation (List.map (convrec env) l)
      | STAR _ x -> PSyn.star (convrec env x)
      | NEG _ x -> PSyn.neg (convrec env x)
      | OPT _ x -> PSyn.disjunction [(convrec env x); PSyn.epsilon]
      | EPS _ -> PSyn.epsilon
      | LETIN _ s e1 e2 ->
         convrec [(s,convrec env e1) :: env] e2
      | ID loc s -> match List.assoc s env with [
           exception Not_found ->
                     raise_failwithf loc "Llk_regexps.normalize_astre: unrecognized ID: %s" s
         | e -> e
         ]
      ]
  in convrec env x
;
