(* camlp5r *)
(* pp_MLast.ml,v *)

include Pa_ppx_base.Pp_MLast

module Ploc : sig
include (module type of Ploc with type t = Ploc.t)

val compare : t -> t -> bool
type 'a vala = [%import: 'a Ploc.vala] [@@deriving ord]
end

type loc = [%import: MLast.loc] [@@deriving ord]
type type_var = [%import: MLast.type_var] [@@deriving ord]

[%%import: MLast.expr] [@@deriving ord]
