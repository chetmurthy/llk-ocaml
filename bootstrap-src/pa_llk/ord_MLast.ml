(* camlp5r *)
(* ord_MLast.ml,v *)

open Pa_ppx_base.Pp_MLast

module Ploc = struct
include Ploc

let compare (x : t) y = 0

type 'a vala = [%import: 'a Ploc.vala] [@@deriving ord]
end

type loc = [%import: MLast.loc] [@@deriving ord]
type type_var = [%import: MLast.type_var] [@@deriving ord]

[%%import: MLast.expr] [@@deriving ord]
