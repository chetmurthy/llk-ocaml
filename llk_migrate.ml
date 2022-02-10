open MLast
open Llk_types

let _migrate_list subrw0 __dt__ l =
  List.map (subrw0 __dt__) l

[%%import: Llk_types.a_symbol
  [@with Ord_MLast.patt := patt]
  [@with Ord_MLast.expr := expr]
]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_open_recursion = true
    ; default_dispatchers = [
        {
          srcmod = Llk_types
        ; dstmod = Llk_types
        ; types = [
            a_position
          ; a_assoc
          ; a_entry
          ; a_level
          ; a_rule
          ; a_rules
          ; a_psymbol
          ; a_symbol
          ]
        }
      ]
    ; dispatchers = {
        migrate_option = {
          srctype = [%typ: 'a option]
        ; dsttype = [%typ: 'b option]
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        ; code = (fun subrw __dt__ x -> Option.map (subrw __dt__) x)
        }
      ; migrate_list = {
          srctype = [%typ: 'a list]
        ; dsttype = [%typ: 'b list]
        ; code = _migrate_list
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        }
      ; migrate_loc = {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
        }
      ; migrate_patt = {
          srctype = [%typ: patt]
        ; dsttype = [%typ: patt]
        ; code = fun __dt__ x -> x
        }
      ; migrate_expr = {
          srctype = [%typ: expr]
        ; dsttype = [%typ: expr]
        ; code = fun __dt__ x -> x
        }
      ; migrate_lmin_len = {
          srctype = [%typ: lmin_len]
        ; dsttype = [%typ: lmin_len]
        ; code = fun __dt__ x -> x
        }
      }
    }
]

