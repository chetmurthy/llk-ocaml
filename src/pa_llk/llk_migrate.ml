open MLast
open Llk_types

let _migrate_list subrw0 __dt__ l =
  List.map (subrw0 __dt__) l


module Camlp5 = struct
module Ploc= struct
include Ploc

let pp ppf x = Fmt.(const string "<loc>" ppf ())
end

[%%import: MLast.expr
    [@add [%%import: MLast.loc]]
    [@add [%%import: MLast.type_var]]
    [@add [%%import: 'a Ploc.vala]]
    [@with Ploc.vala := vala]
]
[@@deriving migrate
    { dispatch_type = dispatch_table_t
    ; dispatch_table_constructor = make_dt
    ; default_dispatchers = [
        {
          srcmod = MLast
        ; dstmod = MLast
        ; types = [
            class_infos
          ; longid
          ; ctyp
          ; poly_variant
          ; patt
          ; expr
          ; case_branch
          ; module_type
          ; functor_parameter
          ; sig_item
          ; with_constr
          ; module_expr
          ; str_item
          ; type_decl
          ; generic_constructor
          ; extension_constructor
          ; type_extension
          ; class_type
          ; class_sig_item
          ; class_expr
          ; class_str_item
          ; longid_lident
          ; payload
          ; attribute_body
          ; attribute
          ; attributes_no_anti
          ; attributes
          ; type_var
          ; vala
          ]
        }
      ]
    ; dispatchers = {
        migrate_list = {
          srctype = [%typ: 'a list]
        ; dsttype = [%typ: 'b list]
        ; code = _migrate_list
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        }
      ; migrate_option = {
          srctype = [%typ: 'a option]
        ; dsttype = [%typ: 'b option]
        ; subs = [ ([%typ: 'a], [%typ: 'b]) ]
        ; code = (fun subrw __dt__ x -> Option.map (subrw __dt__) x)
        }
      ; migrate_loc = {
          srctype = [%typ: loc]
        ; dsttype = [%typ: loc]
        ; code = fun __dt__ x -> x
        }
      }
    }
]
end

[%%import: Llk_types.a_symbol
  [@add [%%import: Llk_regexps.astre]]
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
      ; {
          srcmod = Llk_regexps
        ; dstmod = Llk_regexps
        ; types = [
            astre
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
