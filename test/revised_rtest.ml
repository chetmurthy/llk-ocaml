
open Asttools;
open Pcaml;
open Mlsyntax.Revised;

value with_value r newv f arg = do {
    let oldv = r.val in
    r.val := newv ;
    let rv = f arg in
    r.val := oldv ;
    rv
  }
;

value gram =
 with_value Plexer.dollar_for_antiquotation False
   (with_value Plexer.simplest_raw_strings False
      (with_value Plexer.utf8_lexing True
         (fun () -> Grammar.gcreate (Plexer.gmake()))
      )
   )
   ()
;

value mksequence2 loc =
  fun
  [ <:vala< [e] >> → e
  | seq → <:expr< do { $_list:seq$ } >> ]
;

value mksequence loc =
  fun
  [ [e] → e
  | el → <:expr< do { $list:el$ } >> ]
;

value mkmatchcase loc p aso w e =
  let p =
    match aso with
    [ Some p2 → <:patt< ($p$ as $p2$) >>
    | None → p ]
  in
  (p, w, e)
;

value neg_string n =
  let len = String.length n in
  if len > 0 && n.[0] = '-' then String.sub n 1 (len - 1) else "-" ^ n
;

value mklistexp loc last =
  loop True where rec loop top =
    fun
    [ [] →
        match last with
        [ Some e → e
        | None → <:expr< [] >> ]
    | [e1 :: el] →
        let loc = if top then loc else Ploc.encl (MLast.loc_of_expr e1) loc in
        <:expr< [$e1$ :: $loop False el$] >> ]
;

value mklistpat loc last =
  loop True where rec loop top =
    fun
    [ [] →
        match last with
        [ Some p → p
        | None → <:patt< $uid:"[]"$ >> ]
    | [p1 :: pl] →
        let loc = if top then loc else Ploc.encl (MLast.loc_of_patt p1) loc in
        <:patt< [$p1$ :: $loop False pl$] >> ]
;

value mktupexp loc e el = <:expr< ($list:[e::el]$) >>;
value mktuppat loc p pl = <:patt< ($list:[p::pl]$) >>;
value mktuptyp loc t tl = <:ctyp< ( $list:[t::tl]$ ) >>;

value mklabdecl loc i mf t attrs = (loc, i, mf, t, attrs);
value mkident i : string = i;

value rec generalized_type_of_type =
  fun
  [ <:ctyp< $t1$ → $t2$ >> →
      let (tl, rt) = generalized_type_of_type t2 in
      ([t1 :: tl], rt)
  | t → ([], t) ]
;

value warned = ref False;
value warning_deprecated_since_6_00 loc =
  if not warned.val then do {
    Pcaml.warning.val loc "syntax deprecated since version 6.00";
    warned.val := True
  }
  else ()
;

value build_op_attributed loc op attrs =
  List.fold_left (fun e a -> <:expr< $e$ [@ $attribute:a$ ] >>)
          <:expr< $lid:op$ >> attrs  
;

value build_letop_binder loc letop b l e =
  let (argpat, argexp) = (* TODO FIX THIS CHET *)
    List.fold_left (fun (argpat, argexp) (andop, (pat, exp)) ->
        (<:patt< ( $argpat$, $pat$ ) >>, <:expr< $lid:andop$ $argexp$ $exp$ >>))
      b l in
  <:expr< $lid:letop$ $argexp$ (fun $argpat$ -> $e$) >>
;

value stream_peek_nth n strm =
  loop n (Stream.npeek n strm) where rec loop n =
    fun
    [ [] -> None
    | [x] -> if n == 1 then Some x else None
    | [_ :: l] -> loop (n - 1) l ]
;

value patt_wrap_attrs loc e l =
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:patt< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value patt_to_inline loc p ext attrs =
  let p = patt_wrap_attrs loc p attrs in
  match ext with [ None -> p
  | Some attrid ->
   <:patt< [% $attrid:attrid$ ? $patt:p$ ] >>
  ]
;

value class_expr_wrap_attrs loc e l =
let rec wrec e = fun [
  [] -> e
| [h :: t] -> wrec <:class_expr< $e$ [@ $_attribute:h$ ] >> t
] in wrec e l
;

value str_item_to_inline loc si ext =
  match ext with [ None -> si
  | Some attrid ->
   <:str_item< [%% $attrid:attrid$ $stri:si$ ; ] >>
  ]
;


value quotation_content s =
  loop 0 where rec loop i =
    if i = String.length s then ("", s)
    else if s.[i] = ':' || s.[i] = '@' then
      let i = i + 1 in
      (String.sub s 0 i, String.sub s i (String.length s - i))
    else loop (i + 1)
;

[@@@llk
{foo|
GRAMMAR Revised:
EXTEND gram ;
  EXPORT: sig_item str_item ctyp patt expr functor_parameter module_type
    module_expr longident longident_lident extended_longident signature
    structure class_type class_expr class_expr_simple class_sig_item class_str_item let_binding
    type_decl type_extension extension_constructor
    constructor_declaration label_declaration match_case ipatt
    with_constr poly_variant attribute_body alg_attribute alg_attributes
    operator_rparen
    ext_attributes
    interf implem use_file top_phrase
    ;
REGEXPS:
  check_additive_rparen = ("+" | "-" | "+." | "-." | "+=") ")" ;
  check_type_binder =
         let tyvar = "'" (LIDENT | UIDENT) | GIDENT in
         (tyvar tyvar * | ($list | $_list)) "."
  ;
  check_type_decl =
         let tyvar = "'" (LIDENT | UIDENT) | GIDENT in
         let type_parameter = ("+"|"-"|"!"|"!+"|"+!"| "!-"|"-!")* (tyvar | "_") in
         let type_parameters = ($list | $_list | type_parameter* ) in
         let v_flag_nonrec = ($flag | $_flag | "nonrec")? in
         let type_patt = $tp | $_tp | $lid | $_lid | LIDENT in
         v_flag_nonrec type_patt type_parameters
  ;
  v_uident = $uid | $_uid | UIDENT ;
  v_longident = (v_uident ".") * v_uident ;
  v_lident = $lid | $_lid | LIDENT ;
  v_longident_lident = (v_longident ".")? v_lident ;
  check_type_extension =
         let tyvar = "'" (LIDENT | UIDENT) | GIDENT in
         let type_parameter = ("+"|"-"|"!"|"!+"|"+!"| "!-"|"-")* (tyvar | "_") in
         let type_parameters = ($list | $_list | type_parameter* ) in
         v_longident_lident type_parameters "+="
  ;
  check_uident_coloneq = (UIDENT | $uid | $_uid) ":=" ;
  check_let_exception = "let" "exception" ;
  check_lbracket = "[" ;
  check_lbrace = "{" ;
  check_lbracketbar = "[|" ;
  check_dot_uid =  "." (UIDENT | $uid | $_uid) ;
  check_lident_colon = LIDENT ":" ;
  check_colon = ":" ;
  check_lparen_type = "(" "type" ;

  check_sig_item = "exception" | "type" (check_type_decl | check_type_extension) | "[%%" | "[@@@" | "declare" | "external" | "include" | "module" | "open" | "value" | $_signature | $signature | "class" ;
  check_ctyp = "'" | LIDENT | UIDENT | GIDENT | "!" | "_" | $lid | $_lid | $uid | $_uid | "[" | "{" | "(" | "type" | "#" | QUESTIONIDENTCOLON | TILDEIDENTCOLON | ".." | "<" | "[%" | $"?:" | $"_?:" | $_type | $"_~:" | $"type" | $"~:" ;

  check_arrow = "->" ;
  check_eps = eps ;

  check_infix_operator0 = 
      INFIXOP0 
    | "!=" 
    | "<>" 
    | "=" 
    | "<" 
    | ">" 
    | "||" 
    | "or" 
    | "&" 
    | "&&" 
    ;
  check_infix_operator1 =
      INFIXOP1 
    | "@" 
    | "^" 
    ;
  check_additive_operator2 =
      "+" 
    | "+=" 
    | "-" 
    | "+." 
    | "-." 
    ;
  check_infix_operator2 =
      INFIXOP2 
    | check_additive_operator2
    ;
  check_infix_operator3 =
      INFIXOP3
    | "lor" 
    | "lxor" 
    | "mod" 
    | "land" 
    | "*" 
    | "/" 
    | "%" 
    ;
  check_infix_operator4 =
      INFIXOP4 
    | "asr" 
    | "lsl" 
    | "lsr" 
    | "**" 
    ;
  check_prefix_operator =
      PREFIXOP 
    | "!" 
    ;
  check_infix_operator =
      check_infix_operator0 
    | check_infix_operator1 
    | check_infix_operator2 
    | check_infix_operator3 
    | check_infix_operator4 
    | ":=" 
    ;
  check_operator =
      check_prefix_operator 
    | check_infix_operator 
    | HASHOP 
    | LETOP 
    | ANDOP 
    | "::" 
    | DOTOP "(" ")" 
    | DOTOP "(" ")" "<-" 
    | DOTOP "(" ";" ".." ")" 
    | DOTOP "(" ";" ".." ")" "<-" 

    | DOTOP "{" "}" 
    | DOTOP "{" "}" "<-" 
    | DOTOP "{" ";" ".." "}" 
    | DOTOP "{" ";" ".." "}" "<-" 

    | DOTOP "[" "]" 
    | DOTOP "[" "]" "<-" 
    | DOTOP "[" ";" ".." "]" 
    | DOTOP "[" ";" ".." "]" "<-" 
    ;
  check_operator_rparen =
      check_operator ")"
  ;
  check_hash_v_lident = "#" (LIDENT | $lid | $_lid) ;
  check_hash_lident = "#" LIDENT ;
  check_question_lbrace = "?" "{" ;
END;

  infix_operator0: [ [
      x = INFIXOP0 -> x
    | "!=" -> "!="
    | "<>" -> "<>"
    | "=" -> "="
    | "<" -> "<"
    | ">" -> ">"
    | "||" -> "||"
    | "or" -> "or"
    | "&" -> "&"
    | "&&" -> "&&"
(* NOTE WELL: "$" is not a supported operator in Camlp5's revised syntax,
   b/c conflicts with antiquotations, e.g. <:expr< a $ $lid:id$ >> would
   *suck* to parse
    | "$" -> "$"
 *)
    ] ]
    ;
  infix_operator1: [ [
      x = INFIXOP1 -> x
    | "@" -> "@"
    | "^" -> "^"
    ] ]
    ;
  additive_operator2: [ [
      "+" -> "+"
    | "+=" -> "+="
    | "-" -> "-"
    | "+." -> "+."
    | "-." -> "-."
    ] ]
    ;
  infix_operator2: [ [
      x = INFIXOP2 -> x
    | check_additive_rparen ; x = additive_operator2 -> x
    ] ]
    ;
  infix_operator3: [ [
      x = INFIXOP3 -> x
    | "lor" -> "lor"
    | "lxor" -> "lxor"
    | "mod" -> "mod"
    | "land" -> "land"
    | "*" -> "*"
    | "/" -> "/"
    | "%" -> "%"
    ] ]
    ;
  infix_operator4: [ [
      x = INFIXOP4 -> x
    | "asr" -> "asr"
    | "lsl" -> "lsl"
    | "lsr" -> "lsr"
    | "**" -> "**"
    ] ]
    ;
  prefix_operator: [ [
      x = PREFIXOP -> x
    | "!" -> "!"
    ] ]
    ;
  infix_operator: [ [ 
      x = infix_operator0 -> x
    | x = infix_operator1 -> x
    | x = infix_operator2 -> x
    | x = infix_operator3 -> x
    | x = infix_operator4 -> x
    | ":=" -> ":="
    ] ]
    ;
  operator: [ [
      x = prefix_operator -> x
    | x = infix_operator -> x
    | x = HASHOP -> x
    | op = LETOP -> op
    | op = ANDOP -> op
    | op = "::" -> op

    | op = DOTOP ; "(" ; ")" -> op ^ "()"
    | op = DOTOP ; "(" ; ")" ; "<-" -> op ^ "()<-"
    | op = DOTOP ; "(" ; ";" ; ".." ; ")" -> op ^ "(;..)"
    | op = DOTOP ; "(" ; ";" ; ".." ; ")" ; "<-" -> op ^ "(;..)<-"

    | op = DOTOP ; "{" ; "}" -> op ^ "{}"
    | op = DOTOP ; "{" ; "}" ; "<-" -> op ^ "{}<-"
    | op = DOTOP ; "{" ; ";" ; ".." ; "}" -> op ^ "{;..}"
    | op = DOTOP ; "{" ; ";" ; ".." ; "}" ; "<-" -> op ^ "{;..}<-"

    | op = DOTOP ; "[" ; "]" -> op ^ "[]"
    | op = DOTOP ; "[" ; "]" ; "<-" -> op ^ "[]<-"
    | op = DOTOP ; "[" ; ";" ; ".." ; "]" -> op ^ "[;..]"
    | op = DOTOP ; "[" ; ";" ; ".." ; "]" ; "<-" -> op ^ "[;..]<-"
    ] ]
    ;
  operator_rparen: [ [
      op = operator ; ")" -> op
    ] ]
    ;

  attribute_id:
  [ [ l = GREEDY LIST1 [ i = LIDENT -> i | i = UIDENT -> i ] SEP "." -> (loc, String.concat "." l)
    | s = STRING -> (loc, s)
    ] ]
  ;
  attribute_structure:
    [ [ st = V (LIST1 [ s = str_item; ";" → s ]) "structure" → st ] ]
  ;
  attribute_signature:
    [ [ st = V (LIST1 [ s = sig_item; ";" → s ]) "signature" → st ] ]
  ;
  attribute_body:
  [ [
      id = V attribute_id "attrid" ; st = attribute_structure ->
      <:attribute_body< $_attrid:id$ $_structure:st$ >>
    | id = V attribute_id "attrid" ->
      <:attribute_body< $_attrid:id$ >>
    | id = V attribute_id "attrid" ; ":" ; check_sig_item ; si = attribute_signature -> 
      <:attribute_body< $_attrid:id$ : $_signature:si$ >>
    | id = V attribute_id "attrid" ; ":" ; check_ctyp ; ty = V ctyp "type" -> 
      <:attribute_body< $_attrid:id$ : $_type:ty$ >>
    | id = V attribute_id "attrid" ; ([ "?" ; patt ])? ; "?" ;  p = V patt "patt" -> 
      <:attribute_body< $_attrid:id$ ? $_patt:p$ >>
    | id = V attribute_id "attrid" ; ([ "?" ; patt ])? ; "?" ;  p = V patt "patt"; "when"; e = V expr "expr" -> 
      <:attribute_body< $_attrid:id$ ? $_patt:p$ when $_expr:e$ >>
    ] ]
  ;
  floating_attribute:
  [ [ "[@@@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  alg_attribute:
  [ [ "[@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attribute:
  [ [ "[@@" ; attr = V attribute_body "attribute"; "]" -> attr
    ] ]
  ;
  item_attributes:
  [ [ l = V (GREEDY LIST0 item_attribute) "itemattrs" -> l ]
  ]
  ;
  alg_attributes:
  [ [ l = V (GREEDY LIST0 alg_attribute) "algattrs" -> l ]
  ]
  ;
  alg_attributes_no_anti:
  [ [ l = (GREEDY LIST0 alg_attribute) -> l ]
  ]
  ;
  item_extension:
  [ [ "[%%" ; e = V attribute_body "extension"; "]" -> e
    ] ]
  ;
  alg_extension:
  [ [ "[%" ; e = V attribute_body "extension"; "]" -> e
    ] ]
  ;
  functor_parameter:
    [ [ "("; i = V uidopt "uidopt"; ":"; t = module_type; ")" -> Some(i, t)
      | "("; ")" -> None
      ]
    ]
  ;
  module_expr:
    [ [ "functor"; arg = V functor_parameter "functor_parameter" "fp"; "->";
        me = SELF →
           <:module_expr< functor $_fp:arg$ → $me$ >>
      | x = NEXT -> x
      ]
    | "alg_attribute" GREEDY LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | [ "struct"; st = structure; "end" →
          <:module_expr< struct $_list:st$ end >>
      | x = NEXT -> x
      ]
    | LEFTA [ me1 = SELF; me2 = SELF → <:module_expr< $me1$ $me2$ >> ]
    | LEFTA [ me1 = SELF; "."; me2 = SELF → <:module_expr< $me1$ . $me2$ >> ]
    | "simple"
      [ i = V UIDENT → <:module_expr< $_uid:i$ >>
      | "("; "value"; e = expr; ":"; mt1 = module_type; ":>"; mt2 = module_type; ")" →
          <:module_expr< (value $e$ : $mt1$ :> $mt2$) >>
      | "("; "value"; e = expr; ":"; mt1 = module_type; ")" →
          <:module_expr< (value $e$ : $mt1$) >>
      | "("; "value"; e = expr; ")" →
          <:module_expr< (value $e$) >>
      | "("; me = module_expr; ":"; mt = module_type; ")" →
          <:module_expr< ( $me$ : $mt$ ) >>
      | "("; me = module_expr; ")" → <:module_expr< $me$ >>
      | e = alg_extension -> <:module_expr< [% $_extension:e$ ] >>
      ] ]
  ;
  structure:
    [ [ st = V (LIST0 [ s = str_item; ";" → s ]) → st ] ]
  ;

  type_binder_opt: [ [
    check_type_binder ; ls = V (LIST1 typevar) ; "." -> ls
  | check_eps -> <:vala< [] >>
  ] ]
  ;
  str_item:
    [ "top"
      [ "declare"; st = V (LIST0 [ s = str_item; ";" → s ]); "end" →
          <:str_item< declare $_list:st$ end >>
      | "exception"; ec = V extension_constructor "excon" ; item_attrs = item_attributes →
          <:str_item< exception $_excon:ec$ $_itemattrs:item_attrs$ >>

      | "external"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:str_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "external"; "("; i = operator_rparen; ":"; ls = type_binder_opt; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:str_item< external $lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "include"; me = module_expr ; attrs = item_attributes → <:str_item< include $me$ $_itemattrs:attrs$ >>
      | "module"; r = V (FLAG "rec"); l = V (LIST1 mod_binding SEP "and") →
          <:str_item< module $_flag:r$ $_list:l$ >>
      | "module"; "type"; i = V ident "";  "="; mt = module_type ; attrs = item_attributes →
          <:str_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >>
      | "open"; ovf = V (FLAG "!") "!"; me = module_expr; attrs = item_attributes ->
          <:str_item< open $_!:ovf$ $me$ $_itemattrs:attrs$ >>
      | "type"; check_type_decl ; nrfl = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") → do {
          vala_it (fun tdl ->
            if List.exists (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl then
              failwith "type-declaration cannot mix decl and subst"
            else ()) tdl ;
            <:str_item< type $_flag:nrfl$ $_list:tdl$ >>
          }
      | "type" ; check_type_extension ; te = type_extension →
          <:str_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >>
      | "value"; ext = ext_opt; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and") ->
          str_item_to_inline loc <:str_item< value $_flag:r$ $_list:l$ >> ext

      | e = expr ; attrs = item_attributes → <:str_item< $exp:e$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension ; attrs = item_attributes ->
        <:str_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >>
      | e = NEXT -> e
      ]
    | [ ]
    ]
  ;
  mod_binding:
    [ [ i = V uidopt "uidopt"; me = mod_fun_binding ;
        attrs = item_attributes → (i, me, attrs)
      ] ]
  ;
  mod_fun_binding:
    [ RIGHTA
      [ arg = V functor_parameter "functor_parameter" "fp"; mb = SELF →
          <:module_expr< functor $_fp:arg$ → $mb$ >> ]
    | [ ":"; mt = module_type; "="; me = module_expr →
          <:module_expr< ( $me$ : $mt$ ) >>
      | "="; me = module_expr → <:module_expr< $me$ >> ] ]
  ;
  module_type:
    [ RIGHTA [ "functor"; arg = V functor_parameter "functor_parameter" "fp" ; "->";
        mt = SELF →
          <:module_type< functor $_fp:arg$ → $mt$ >>
      ]
    | "->" NONA
       [ mt1=NEXT ; PRIORITY 1 ; "->" ; mt2=SELF ->
         <:module_type< $mt1$ → $mt2$ >>
       | mt1=NEXT -> mt1
       ]
    | "alg_attribute" GREEDY LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:module_type< $e1$ [@ $_attribute:attr$ ] >>
      | e1 = SELF; "with"; wcl = V (GREEDY LIST1 with_constr SEP "and") →
          <:module_type< $e1$ with $_list:wcl$ >>
      ]
    | [ "sig"; sg = signature; "end" →
          <:module_type< sig $_list:sg$ end >>
      | "module"; "type"; "of"; me = module_expr →
          <:module_type< module type of $me$ >>
      | x = NEXT -> x
      ]
    | "simple"
      [ li = extended_longident; PRIORITY 1 ; "."; i = V LIDENT → <:module_type< $longid:li$ . $_lid:i$ >>
      | li = extended_longident → <:module_type< $longid:li$ >>
      | i = V LIDENT → <:module_type< $_lid:i$ >>
      | e = alg_extension -> <:module_type< [% $_extension:e$ ] >>
      | "'"; i = V ident "" → <:module_type< ' $_:i$ >>
      | "("; mt = module_type; ")" → <:module_type< $mt$ >> ] ]
  ;
  signature:
    [ [ st = V (LIST0 [ s = sig_item; ";" → s ]) → st ] ]
  ;
  sig_item:
    [ "top"
      [ "declare"; st = V (LIST0 [ s = sig_item; ";" → s ]); "end" →
          <:sig_item< declare $_list:st$ end >>
      | "exception"; gc = constructor_declaration ; item_attrs = item_attributes →
          MLast.SgExc loc gc item_attrs
      | "external"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:sig_item< external $_lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "external"; "("; i = operator_rparen; ":"; ls = type_binder_opt ; t = ctyp; "=";
        pd = V (LIST1 STRING) ; attrs = item_attributes →
          <:sig_item< external $lid:i$ : $_list:ls$ . $t$ = $_list:pd$ $_itemattrs:attrs$ >>

      | "include"; mt = module_type ; attrs = item_attributes → <:sig_item< include $mt$ $_itemattrs:attrs$ >>
      | "module"; rf = V (FLAG "rec");
        l = V (LIST1 mod_decl_binding SEP "and") →
          <:sig_item< module $_flag:rf$ $_list:l$ >>

      | "module"; check_uident_coloneq ; i = V UIDENT "uid" ; ":="; li = extended_longident ; attrs = item_attributes →
        <:sig_item< module $_uid:i$ := $longid:li$ $_itemattrs:attrs$ >>

      | "module"; "type"; i = V ident ""; "="; mt = module_type ; attrs = item_attributes →
          <:sig_item< module type $_:i$ = $mt$ $_itemattrs:attrs$ >>
      | "module"; "type"; i = V ident ""; ":="; mt = module_type ; attrs = item_attributes →
          <:sig_item< module type $_:i$ := $mt$ $_itemattrs:attrs$ >>
      | "module"; "alias"; i = V UIDENT "uid"; "="; li = V longident "longid" ; attrs = item_attributes →
          <:sig_item< module alias $_uid:i$ = $_longid:li$ $_itemattrs:attrs$ >>
      | "open"; i = extended_longident ; attrs = item_attributes → 
          <:sig_item< open $longid:i$ $_itemattrs:attrs$ >>
      | "type"; check_type_decl ; nrfl = V (FLAG "nonrec"); tdl = V (LIST1 type_decl SEP "and") → do {
            vala_it (fun tdl ->
              if List.for_all (fun td -> Pcaml.unvala td.MLast.tdIsDecl) tdl then ()
              else if List.for_all (fun td -> not (Pcaml.unvala td.MLast.tdIsDecl)) tdl then
                vala_it (fun nrfl ->
                    if nrfl then failwith "type-subst declaration must not specify <<nonrec>>" else ()) nrfl
              else failwith "type-declaration cannot mix decl and subst") tdl ;
            <:sig_item< type $_flag:nrfl$ $_list:tdl$ >>
          }
      | "type" ; check_type_extension ; te = type_extension →
          <:sig_item< type $_lilongid:te.MLast.teNam$ $_list:te.MLast.tePrm$ += $_priv:te.MLast.tePrv$ [ $_list:te.MLast.teECs$ ] $_itemattrs:te.MLast.teAttributes$ >>
      | "value"; i = V LIDENT "lid" ""; ":"; ls = type_binder_opt ; t = ctyp ; attrs = item_attributes →
        let t = match Pcaml.unvala ls with [ [] -> t | _ -> <:ctyp< ! $_list:ls$ . $t$ >> ] in
          <:sig_item< value $_lid:i$ : $t$ $_itemattrs:attrs$ >>

      | "value"; "("; i = operator_rparen; ":"; ls = type_binder_opt ; t = ctyp ; attrs = item_attributes →
        let t = match Pcaml.unvala ls with [ [] -> t | _ -> <:ctyp< ! $_list:ls$ . $t$ >> ] in
          <:sig_item< value $lid:i$ : $t$ $_itemattrs:attrs$ >>

      | attr = floating_attribute -> <:sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension ; attrs = item_attributes ->
        <:sig_item< [%% $_extension:e$ ] $_itemattrs:attrs$ >>
      | x = NEXT -> x
      ]
    | [ ]
    ]
  ;
  mod_decl_binding:
    [ [ i = V uidopt "uidopt"; mt = module_declaration ; attrs = item_attributes → (i, mt, attrs) ] ]
  ;
  module_declaration:
    [ RIGHTA
      [ arg = V functor_parameter "functor_parameter" "fp" ; mt = SELF →
          <:module_type< functor $_fp:arg$ → $mt$ >>
      ]
    | [ ":"; mt = module_type → <:module_type< $mt$ >> ] ]
  ;
  with_constr:
    [ [ "type"; i = V longident_lident "lilongid"; tpl = V (LIST0 type_parameter);
        "="; pf = V (FLAG "private"); t = ctyp_below_alg_attribute →
          <:with_constr< type $_lilongid:i$ $_list:tpl$ = $_flag:pf$ $t$ >>
      | "type"; i = V longident_lident "lilongid"; tpl = V (LIST0 type_parameter);
        ":="; t = ctyp_below_alg_attribute →
          <:with_constr< type $_lilongid:i$ $_list:tpl$ := $t$ >>
      | "module"; li = V longident "longid"; "="; me = module_expr →
          <:with_constr< module $_longid:li$ = $me$ >>
      | "module"; li = V longident "longid"; ":="; me = module_expr →
          <:with_constr< module $_longid:li$ := $me$ >>
      | "module"; "type"; li = V longident "longid"; "="; mt = module_type →
          <:with_constr< module type $_longid:li$ = $mt$ >>
      | "module"; "type"; li = V longident "longid"; ":="; mt = module_type →
          <:with_constr< module type $_longid:li$ := $mt$ >>
      ] ]
  ;
  uidopt:
    [ [ m = V UIDENT -> Some m
      | "_" -> None
      ]
    ]
  ;
  andop_binding:
  [ [ op = ANDOP ; b = letop_binding -> (op, b) ] ]
  ;
  ext_opt: [ [ ext = OPT [ "%" ; id = attribute_id -> id ] -> ext ] ] ;
  ext_attributes: [ [ e = ext_opt ; l = alg_attributes_no_anti -> (e, l) ] ] ;
  expr:
    [ "top" NONA
      [ check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ;
        "of" ; tyl = V (GREEDY LIST1 ctyp_below_alg_attribute) ; alg_attrs = alg_attributes ; "in" ; x = SELF ->
        <:expr< let exception $_uid:id$ of $_list:tyl$ $_algattrs:alg_attrs$ in $x$ >>
      | check_let_exception ; "let" ; "exception" ; id = V UIDENT "uid" ; alg_attrs = alg_attributes ;
        "in" ; x = SELF ->
        <:expr< let exception $_uid:id$ $_algattrs:alg_attrs$ in $x$ >>

      | "let"; ext = ext_opt ; r = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and"); "in";
        x = SELF →
          expr_to_inline <:expr< let $_flag:r$ $_list:l$ in $x$ >> ext []

      | letop = LETOP ; b = letop_binding ; l = LIST0 andop_binding; "in";
        x = SELF ->
          build_letop_binder loc letop b l x

      | "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in"; e = SELF →
          expr_to_inline <:expr< let module $_uidopt:m$ = $mb$ in $e$ >> ext attrs
      | "let"; "open"; ovf = V (FLAG "!") "!"; (ext,attrs) = ext_attributes; m = module_expr; "in"; e = SELF →
          expr_to_inline <:expr< let open $_!:ovf$ $m$ in $e$ >> ext attrs
      | "fun"; (ext,attrs) = ext_attributes; l = closed_case_list →
          expr_to_inline <:expr< fun [ $_list:l$ ] >> ext attrs
      | "fun"; (ext,attrs) = ext_attributes; p = ipatt; e = fun_def →
          expr_to_inline <:expr< fun $p$ → $e$ >> ext attrs
      | "match"; (ext,attrs) = ext_attributes; e = SELF; "with"; l = closed_case_list →
          expr_to_inline <:expr< match $e$ with [ $_list:l$ ] >> ext attrs
      | "match"; (ext,attrs) = ext_attributes; e = SELF; "with"; p1 = ipatt; "->"; e1 = SELF →
          expr_to_inline <:expr< match $e$ with $p1$ → $e1$ >> ext attrs
      | "try"; (ext,attrs) = ext_attributes; e = SELF; "with"; l = closed_case_list →
          expr_to_inline <:expr< try $e$ with [ $_list:l$ ] >> ext attrs
      | "try"; (ext,attrs) = ext_attributes; e = SELF; "with"; (patt)? ; mc = match_case →
          expr_to_inline <:expr< try $e$ with [ $list:[mc]$ ] >> ext attrs
      | "if"; (ext,attrs) = ext_attributes; e1 = SELF; "then"; e2 = SELF; "else"; e3 = SELF →
          expr_to_inline <:expr< if $e1$ then $e2$ else $e3$ >> ext attrs
      | "do"; (ext,attrs) = ext_attributes; "{"; seq = V sequence "list"; "}" →
         expr_to_inline (mksequence2 loc seq) ext attrs
      | "for"; (ext,attrs) = ext_attributes; i = patt; "="; e1 = SELF; df = V direction_flag "to";
        e2 = SELF; "do"; "{"; seq = V sequence "list"; "}" →
          expr_to_inline <:expr< for $i$ = $e1$ $_to:df$ $e2$ do { $_list:seq$ } >> ext attrs
      | "while"; (ext,attrs) = ext_attributes; e = SELF; "do"; "{"; seq = V sequence "list"; "}" →
          expr_to_inline <:expr< while $e$ do { $_list:seq$ } >> ext attrs
      | e = NEXT -> e
      ]
    | "where" GREEDY LEFTA
      [ e = SELF; "where"; (ext,attrs) = ext_attributes; rf = V (FLAG "rec"); lb = where_binding →
          expr_to_inline <:expr< let $_flag:rf$ $list:[lb]$ in $e$ >> ext attrs
      ]
    | ":=" RIGHTA
      [ e1 = SELF; ":="; e2 = SELF → <:expr< $e1$ := $e2$ >> ]
    | "||" RIGHTA
      [ e1 = SELF; "||"; e2 = SELF → <:expr< $e1$ || $e2$ >> ]
    | "&&" RIGHTA
      [ e1 = SELF; "&&"; e2 = SELF → <:expr< $e1$ && $e2$ >> ]
    | "<" LEFTA
      [ e1 = SELF; "<"; e2 = SELF → <:expr< $e1$ < $e2$ >>
      | e1 = SELF; ">"; e2 = SELF → <:expr< $e1$ > $e2$ >>
      | e1 = SELF; "<="; e2 = SELF → <:expr< $e1$ <= $e2$ >>
      | e1 = SELF; ">="; e2 = SELF → <:expr< $e1$ >= $e2$ >>
      | e1 = SELF; "="; e2 = SELF → <:expr< $e1$ = $e2$ >>
      | e1 = SELF; "<>"; e2 = SELF → <:expr< $e1$ <> $e2$ >>
      | e1 = SELF; "=="; e2 = SELF → <:expr< $e1$ == $e2$ >>
      | e1 = SELF; "!="; e2 = SELF → <:expr< $e1$ != $e2$ >>
      | e1 = SELF; op = INFIXOP0; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "^" RIGHTA
      [ e1 = SELF; "^"; e2 = SELF → <:expr< $e1$ ^ $e2$ >>
      | e1 = SELF; "@"; e2 = SELF → <:expr< $e1$ @ $e2$ >>
      | e1 = SELF; op = INFIXOP1; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:expr< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | "+" LEFTA
      [ e1 = SELF; "+"; e2 = SELF → <:expr< $e1$ + $e2$ >>
      | e1 = SELF; "-"; e2 = SELF → <:expr< $e1$ - $e2$ >>
      | e1 = SELF; "+."; e2 = SELF → <:expr< $e1$ +. $e2$ >>
      | e1 = SELF; "-."; e2 = SELF → <:expr< $e1$ -. $e2$ >>
      | e1 = SELF; op = INFIXOP2; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "*" LEFTA
      [ e1 = SELF; "*"; e2 = SELF → <:expr< $e1$ * $e2$ >>
      | e1 = SELF; "/"; e2 = SELF → <:expr< $e1$ / $e2$ >>
      | e1 = SELF; "*."; e2 = SELF → <:expr< $e1$ *. $e2$ >>
      | e1 = SELF; "/."; e2 = SELF → <:expr< $e1$ /. $e2$ >>
      | e1 = SELF; "land"; e2 = SELF → <:expr< $e1$ land $e2$ >>
      | e1 = SELF; "lor"; e2 = SELF → <:expr< $e1$ lor $e2$ >>
      | e1 = SELF; "lxor"; e2 = SELF → <:expr< $e1$ lxor $e2$ >>
      | e1 = SELF; "mod"; e2 = SELF → <:expr< $e1$ mod $e2$ >>
      | e1 = SELF; op = INFIXOP3; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "**" RIGHTA
      [ e1 = SELF; "**"; e2 = SELF → <:expr< $e1$ ** $e2$ >>
      | e1 = SELF; "asr"; e2 = SELF → <:expr< $e1$ asr $e2$ >>
      | e1 = SELF; "lsl"; e2 = SELF → <:expr< $e1$ lsl $e2$ >>
      | e1 = SELF; "lsr"; e2 = SELF → <:expr< $e1$ lsr $e2$ >>
      | e1 = SELF; op = INFIXOP4; e2 = SELF -> <:expr< $lid:op$ $e1$ $e2$ >>
      ]
    | "unary minus" NONA
      [ "-"; e = SELF → <:expr< - $e$ >>
      | "-."; e = SELF → <:expr< -. $e$ >>
      | "+"; e = SELF → 
         match e with [
           <:expr< $int:_$ >> -> e
         | _ ->  <:expr< $lid:"~+"$ $e$ >>
         ]
      | "+."; e = SELF →
         match e with [
           <:expr< $flo:_$ >> -> e
         | _ -> <:expr< $lid:"~+."$ $e$ >>
         ]
      | e = NEXT -> e
      ]
    | "apply" LEFTA
      [ e1 = SELF; e2 = SELF → <:expr< $e1$ $e2$ >> ]
    | "lazy" NONA
      [ "assert"; (ext,attrs) = ext_attributes; e = SELF →
          expr_to_inline <:expr< assert $e$ >> ext attrs
      | "lazy"; (ext,attrs) = ext_attributes; e = NEXT → 
          expr_to_inline <:expr< lazy $e$ >> ext attrs
      | e = NEXT -> e
      ]
    | "." GREEDY LEFTA
      [ e1 = SELF; "."; lili = V longident_lident "lilongid" ->
        <:expr< $e1$ . $_lilongid:lili$ >>
      | e1 = SELF; "."; "("; check_operator_rparen ; op = operator_rparen ->
          if op = "::" then
            Ploc.raise loc (Failure ".(::) (dot paren colon colon paren) cannot appear except after longident")
          else
            <:expr< $e1$ . $lid:op$ >>

      | e1 = SELF; "."; "("; e2 = SELF; ")" ->
          if expr_last_is_uid e1 then
            failwith "internal error in original-syntax parser at dot-lparen"
          else
            <:expr< $e1$ .( $e2$ ) >>

      | e1 = SELF; op = V DOTOP "dotop"; "("; el = V (LIST1 expr LEVEL "+" SEP ";"); ")" ->
          <:expr< $e1$ $_dotop:op$ ( $_list:el$ ) >>

      | e1 = SELF; "."; "["; e2 = SELF; "]" -> <:expr< $e1$ .[ $e2$ ] >>

      | e1 = SELF; op = V DOTOP "dotop"; "["; el = V (LIST1 expr LEVEL "+" SEP ";"); "]" ->
          <:expr< $e1$ $_dotop:op$ [ $_list:el$ ] >>

      | e1 = SELF; "."; "{"; el = V (LIST1 expr LEVEL "+" SEP ","); "}" ->
          <:expr< $e1$ .{ $_list:el$ } >>

      | e1 = SELF; op = V DOTOP "dotop"; "{"; el = V (LIST1 expr LEVEL "+" SEP ";"); "}" ->
          <:expr< $e1$ $_dotop:op$ { $_list:el$ } >>
      ]
    | "~-" NONA
      [ "~-"; e = SELF → <:expr< ~- $e$ >>
      | "~-."; e = SELF → <:expr< ~-. $e$ >>
      | f = PREFIXOP; e = SELF -> <:expr< $lid:f$ $e$ >>
      | e = NEXT -> e
      ]
    | "simple"
      [ s = V INT → <:expr< $_int:s$ >>
      | s = V INT_l → <:expr< $_int32:s$ >>
      | s = V INT_L → <:expr< $_int64:s$ >>
      | s = V INT_n → <:expr< $_nativeint:s$ >>
      | s = V FLOAT → <:expr< $_flo:s$ >>
      | s = V STRING → <:expr< $_str:s$ >>
      | s = V CHAR → <:expr< $_chr:s$ >>
      | "." -> <:expr< . >>
      | e = alg_extension -> <:expr< [% $_extension:e$ ] >>
      | i = V LIDENT → <:expr< $_lid:i$ >>
      | i = V GIDENT → <:expr< $_lid:i$ >>
      | e = expr_longident → e
      | "["; "]" → <:expr< $uid:"[]"$ >>
      | "["; el = LIST1 expr SEP ";"; last = cons_expr_opt; "]" →
          mklistexp loc last el
      | "[|"; el = V (LIST0 expr SEP ";"); "|]" → <:expr< [| $_list:el$ |] >>
      | "{"; lel = V (LIST1 label_expr SEP ";"); "}" →
          <:expr< { $_list:lel$ } >>
      | "{"; "("; e = expr; ")"; "with"; lel = V (LIST1 label_expr SEP ";");
        "}" →
          <:expr< { ($e$) with $_list:lel$ } >>
      | "("; ")" → <:expr< $uid:"()"$ >>
      | "("; "module"; me = module_expr; ":"; mt = module_type; ")" →
          <:expr< (module $me$ : $mt$) >>
      | "("; "module"; me = module_expr; ")" →
          <:expr< (module $me$) >>
      | "("; check_operator_rparen ; op = operator_rparen ->
          if op = "::" then
            <:expr< $uid:op$ >>
          else
            <:expr< $lid:op$ >>
      | "("; e = expr; ":"; t = ctyp; ")" → <:expr< ($e$ : $t$) >>
      | "("; e = expr; ","; el = LIST1 expr SEP ","; ")" → mktupexp loc e el
      | "("; e = expr; ")" → <:expr< $e$ >> ] ]
  ;
  expr_longident:
    [
      [ li = longident -> <:expr< $longid:li$ >>
      | li = longident ; PRIORITY 1 ; "." ; "("; check_operator_rparen ; op = operator_rparen ->
          if op = "::" then
            <:expr< $longid:li$ . $uid:op$ >>
          else
            <:expr< $longid:li$ . $lid:op$ >>

      | li = longident ; PRIORITY 1 ; "." ; "(" ; e = expr ; ")" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; PRIORITY 1 ; "." ; id = V LIDENT "lid" ->
        <:expr< $longid:li$ . $_lid:id$ >>
      | li = longident ; PRIORITY 1 ; "." ; check_lbracket ; e = expr LEVEL "simple" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; PRIORITY 1 ; "." ; check_lbrace ; e = expr LEVEL "simple" -> <:expr< $longid:li$ . ( $e$ ) >>
      | li = longident ; PRIORITY 1 ; "." ; check_lbracketbar ; e = expr LEVEL "simple" -> <:expr< $longid:li$ . ( $e$ ) >>
      ]
    ]
  ;
  closed_case_list:
    [ [ "["; l = V (LIST0 match_case SEP "|"); "]" → l
      | "|"; l = V (LIST0 match_case SEP "|"); "end" → l ] ]
  ;
  cons_expr_opt:
    [ [ "::"; e = expr → Some e
      | → None ] ]
  ;
  sequence:
    [
      [ PRIORITY 1 ; "let"; rf = V (FLAG "rec"); l = V (LIST1 let_binding SEP "and");
        "in"; el = SELF →
          [<:expr< let $_flag:rf$ $_list:l$ in $mksequence loc el$ >>]
      | PRIORITY 1 ; "let"; "module"; (ext,attrs) = ext_attributes; m = V uidopt "uidopt"; mb = mod_fun_binding; "in";
        el = SELF →
          [expr_to_inline <:expr< let module $_uidopt:m$ = $mb$ in $mksequence loc el$ >> ext attrs]
      | PRIORITY 1 ; "let"; "open"; ovf = V (FLAG "!") "!"; (ext,attrs) = ext_attributes; m = module_expr; "in"; el = SELF →
          [expr_to_inline <:expr< let open $_!:ovf$ $m$ in $mksequence loc el$ >> ext attrs]
      | e = expr; ";"; el = SELF → [e :: el]
      | e = expr; ";" → [e]
      | e = expr → [e]
      ]
    ]
  ;
  where_binding:
    [ [ p = ipatt; PRIORITY 1 ; e = fun_binding →
          let (p,e) = match e with [
            <:expr< ( $e$ : $t$ ) >> -> (<:patt< ($p$ : $t$) >>, e)
          | _ -> (p,e)
          ] in
          (p, e, <:vala< [] >>)
      | p = ipatt ; e = fun_binding →
          (p, e, <:vala< [] >>)
      ] ]
  ;
  let_binding:
    [ [ p = ipatt; PRIORITY 1 ; e = fun_binding ; attrs = item_attributes →
          let (p,e) = match e with [
            <:expr< ( $e$ : $t$ ) >> -> (<:patt< ($p$ : $t$) >>, e)
          | _ -> (p,e)
          ] in
          (p, e, attrs)
      | p = ipatt ; e = fun_binding ; attrs = item_attributes →
          (p, e, attrs)
      ] ]
  ;
  letop_binding:
    [ [ p = ipatt; e = fun_binding → (p, e) ] ]
  ;
  fun_binding:
    [ RIGHTA
      [ p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >> ]
    | [ "="; e = expr → <:expr< $e$ >>
      | ":"; t = ctyp; "="; e = expr → <:expr< ($e$ : $t$) >> ] ]
  ;
  match_case:
    [ [ p = patt; aso = as_patt_opt; w = V (OPT when_expr); "->"; e = expr →
          mkmatchcase loc p aso w e
      ] ]
  ;
  as_patt_opt:
    [ [ "as"; p = patt → Some p
      | → None ] ]
  ;
  when_expr:
    [ [ "when"; e = expr → e ] ]
  ;
  label_expr:
    [ [ i = patt_label_ident; e = fun_binding → (i, e) ] ]
  ;
  fun_def:
    [ RIGHTA
      [ p = ipatt; e = SELF → <:expr< fun $p$ → $e$ >> ]
    | [ "->"; e = expr → e ] ]
  ;
  patt_ident: [
    [ s = V LIDENT → <:patt< $_lid:s$ >>
    | s = V GIDENT → <:patt< $_lid:s$ >>
    | li = longident ; "." ; p = patt LEVEL "simple" → 
      match p with [
        <:patt< $uid:i$ >> ->
        let li = <:extended_longident< $longid:li$ . $uid:i$ >> in
        <:patt< $longid:li$ >>
      | _ -> <:patt< $longid:li$ . $p$ >>
      ]
    | li = longident ; PRIORITY 1 ; "("; "type";
      loc_ids = V (LIST1 [ s = LIDENT -> (loc,s) ]) ; ")" → 
      <:patt< $longid:li$ (type $_list:loc_ids$ ) >>
    | li = longident → <:patt< $longid:li$ >>
    ]
  ]
  ;
  patt:
    [ LEFTA
      [ p1 = SELF; "|"; p2 = SELF → <:patt< $p1$ | $p2$ >> ]
    | "alg_attribute" LEFTA
      [ p = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:patt< $p$ [@ $_attribute:attr$ ] >>
      ]
    | NONA
      [ "exception"; (ext,attrs) = ext_attributes; p = NEXT →
        patt_to_inline loc <:patt< exception $p$ >> ext attrs
      | x = NEXT -> x
      ]
    | NONA
      [ p1 = NEXT; ".."; p2 = NEXT → <:patt< $p1$ .. $p2$ >>
      | p1 = NEXT -> p1
      ]
    | LEFTA
      [ p1 = SELF; p2 = SELF → <:patt< $p1$ $p2$ >> ]
    | "simple"
      [ 
        "lazy"; (ext,attrs) = ext_attributes; p = SELF → 
          patt_to_inline loc <:patt< lazy $p$ >> ext attrs
      | p = patt_ident -> p
      | e = alg_extension -> <:patt< [% $_extension:e$ ] >>
      | s = V INT → <:patt< $_int:s$ >>
      | s = V INT_l → <:patt< $_int32:s$ >>
      | s = V INT_L → <:patt< $_int64:s$ >>
      | s = V INT_n → <:patt< $_nativeint:s$ >>
      | s = V FLOAT → <:patt< $_flo:s$ >>
      | s = V STRING → <:patt< $_str:s$ >>
      | s = V CHAR → <:patt< $_chr:s$ >>
      | "+"; s = V INT → <:patt< $_int:s$ >>
      | "+"; s = V FLOAT → <:patt< $_flo:s$ >>
      | "-"; s = INT → <:patt< $int:neg_string s$ >>
      | "-"; s = INT_l → <:patt< $int32:neg_string s$ >>
      | "-"; s = INT_L → <:patt< $int64:neg_string s$ >>
      | "-"; s = INT_n → <:patt< $nativeint:neg_string s$ >>
      | "-"; s = FLOAT → <:patt< $flo:neg_string s$ >>
      | "["; "]" → <:patt< $uid:"[]"$ >>
      | "["; pl = LIST1 patt SEP ";"; last = cons_patt_opt; "]" →
          mklistpat loc last pl
      | "[|"; pl = V (LIST0 patt SEP ";"); "|]" → <:patt< [| $_list:pl$ |] >>
      | "{"; lpl = V (LIST1 label_patt SEP ";"); "}" →
          <:patt< { $_list:lpl$ } >>
      | "("; check_operator_rparen ; op = operator_rparen ->
          if op = "::" then
            <:patt< $uid:op$ >>
          else
            <:patt< $lid:op$ >>
      | "("; p = paren_patt; ")" → p
      | "_" → <:patt< _ >> ] ]
  ;
  paren_patt:
    [ [ p = patt; ":"; t = ctyp → <:patt< ($p$ : $t$) >>
      | p = patt; "as"; p2 = patt → <:patt< ($p$ as $p2$) >>
      | p = patt; ","; pl = LIST1 patt SEP "," → mktuppat loc p pl
      | p = patt → <:patt< $p$ >>
      | "type"; s = V LIDENT → <:patt< (type $_lid:s$) >>
      | "module"; s = V uidopt "uidopt"; ":"; mt = module_type →
          <:patt< (module $_uidopt:s$ : $mt$) >>
      | "module"; s = V uidopt "uidopt" →
          <:patt< (module $_uidopt:s$) >>
      | → <:patt< $uid:"()"$ >>
 ] ]
  ;
  cons_patt_opt:
    [ [ "::"; p = patt → Some p
      | → None ] ]
  ;
  label_patt:
    [ [ i = patt_label_ident; "="; p = patt → (i, p) ] ]
  ;
  patt_label_ident:
    [
      [ p1 = longident; "."; p2 = SELF → <:patt< $longid:p1$ . $p2$ >>
      | i = V LIDENT → <:patt< $_lid:i$ >>
      ] ]
  ;
  ipatt:
    [ "top" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:patt< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | "simple"
      [ p = patt_ident -> p
      | "("; check_operator_rparen ; op = operator_rparen ->
          if op = "::" then
            <:patt< $uid:op$ >>
          else
            <:patt< $lid:op$ >>
      | "{"; lpl = V (LIST1 label_ipatt SEP ";"); "}" →
          <:patt< { $_list:lpl$ } >>
      | "("; p = paren_ipatt; ")" → p
      | e = alg_extension -> <:patt< [% $_extension:e$ ] >>
      | "_" → <:patt< _ >>
      | x = NEXT -> x
      ]
    | [ ]
    ]
  ;
  paren_ipatt:
    [ [ p = ipatt; ":"; t = ctyp → <:patt< ($p$ : $t$) >>
      | p = ipatt; "as"; p2 = ipatt → <:patt< ($p$ as $p2$) >>
      | p = ipatt; ","; pl = LIST1 ipatt SEP "," → mktuppat loc p pl
      | p = ipatt → <:patt< $p$ >>
      | "type"; s = V LIDENT → <:patt< (type $_lid:s$) >>
      | "module"; s  = V uidopt "uidopt"; ":"; mt = module_type →
          <:patt< (module $_uidopt:s$ : $mt$) >>
      | "module"; s = V uidopt "uidopt" →
          <:patt< (module $_uidopt:s$) >>
      | → <:patt< $uid:"()"$ >>
 ] ]
  ;
  label_ipatt:
    [ [ i = patt_label_ident; "="; p = ipatt → (i, p) ] ]
  ;
  type_decl:
    [ [ n = V type_patt "tp"; tpl = V (LIST0 type_parameter);
        isDecl = V [ "=" -> True | ":=" -> False ] "isdecl" ;
        pf = V (FLAG "private") "priv"; tk = ctyp; cl = V (LIST0 constrain) ; attrs = item_attributes →
          <:type_decl< $_tp:n$ $_list:tpl$ $_isdecl:isDecl$ $_priv:pf$ $tk$ $_list:cl$ $_itemattrs:attrs$ >>
      ] ]
  ;
  type_extension:
    [ [ n = V longident_lident "lilongid"; tpl = V (LIST0 type_parameter); "+=";
        pf = V (FLAG "private") "priv"; "[" ; ecs = V (LIST1 extension_constructor SEP "|") ; "]" ;
        attrs = item_attributes →
          <:type_extension< $_lilongid:n$ $_list:tpl$ += $_priv:pf$ [ $_list:ecs$ ] $_itemattrs:attrs$ >>
      ] ]
  ;
  type_patt:
    [ [ n = V LIDENT → (loc, n) ] ]
  ;
  constrain:
    [ [ "constraint"; t1 = ctyp; "="; t2 = ctyp → (t1, t2) ] ]
  ;
  type_parameter:
    [ [ "+"; p = V simple_type_parameter "" -> (p, (Some True, False))
      | "+"; "!" ; p = V simple_type_parameter "" -> (p, (Some True, True))
      | "-"; p = V simple_type_parameter "" -> (p, (Some False, False))
      | "-"; "!" ; p = V simple_type_parameter "" -> (p, (Some False, True))
      | "!" ; p = V simple_type_parameter "" -> (p, (None, True))
      | "!" ; "+" ; p = V simple_type_parameter "" -> (p, (Some True, True))
      | "!" ; "-" ; p = V simple_type_parameter "" -> (p, (Some False, True))
      | "!+" ; p = V simple_type_parameter "" -> (p, (Some True, True))
      | "+!" ; p = V simple_type_parameter "" -> (p, (Some True, True))
      | "!-" ; p = V simple_type_parameter "" -> (p, (Some False, True))
      | "-!" ; p = V simple_type_parameter "" -> (p, (Some False, True))
      | p = V simple_type_parameter "" -> (p, (None, False))
      ] ]
  ;
  simple_type_parameter:
    [ [ "'"; i = ident → Some i
      | i = GIDENT → Some (greek_ascii_equiv i)
      | "_" → None ] ]
  ;
  longident:
    [ LEFTA
      [ me1 = SELF ; check_dot_uid ; "."; i = V UIDENT "uid" → <:extended_longident< $longid:me1$ . $_uid:i$ >> ]
    | [ i = V UIDENT "uid" → <:extended_longident< $_uid:i$ >>
      ] ]
  ;
  extended_longident:
    [ LEFTA
      [ me1 = SELF; "(" ; me2 = SELF ; ")" → <:extended_longident< $longid:me1$ ( $longid:me2$ ) >>
      | me1 = SELF ; check_dot_uid ; "."; i = V UIDENT "uid" → <:extended_longident< $longid:me1$ . $_uid:i$ >>
      ]
    | [ i = V UIDENT "uid" → <:extended_longident< $_uid:i$ >>
      ] ]
  ;
  ctyp_ident:
    [
      [ me1 = extended_longident ; "." ; i = V LIDENT "lid" → 
          <:ctyp< $longid:me1$ . $_lid:i$ >>
      | i = V LIDENT "lid" → 
          <:ctyp< $_lid:i$ >>
      ] 
    ]
  ;
  ctyp:
    [ "top" LEFTA
      [ t1 = SELF; "=="; pf = V (FLAG "private") "priv"; t2 = SELF →
          <:ctyp< $t1$ == $_priv:pf$ $t2$ >> ]
    | "alg_attribute" LEFTA
      [ e1 = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:ctyp< $e1$ [@ $_attribute:attr$ ] >>
      ]
    | "below_alg_attribute" [ t = NEXT -> t ]
    | "as" LEFTA
      [ t1 = SELF; "as"; t2 = SELF → <:ctyp< $t1$ as $t2$ >> ]
    | RIGHTA
      [ "!"; pl = V (LIST1 typevar); "."; t = SELF →
          <:ctyp< ! $_list:pl$ . $t$ >>
      | "type"; pl = V (LIST1 LIDENT); "."; t = SELF →
          <:ctyp< type $_list:pl$ . $t$ >> ]
    | "arrow" NONA
      [ t1 = NEXT; PRIORITY 1 ; "->"; t2 = SELF → <:ctyp< $t1$ → $t2$ >>
      | t1 = NEXT -> t1
      ]
    | "apply" GREEDY LEFTA
      [ t1 = SELF; t2 = SELF → <:ctyp< $t1$ $t2$ >> ]
    | "simple"
      [ t = ctyp_ident → t
      | "'"; i = V ident "" → <:ctyp< '$_:i$ >>
      | i = GIDENT → <:ctyp< '$greek_ascii_equiv i$ >>
      | ".." -> <:ctyp< .. >>
      | "_" → <:ctyp< _ >>
      | e = alg_extension -> <:ctyp< [% $_extension:e$ ] >>
      | "(" ; "module"; mt = module_type ; ")" → <:ctyp< ( module $mt$ ) >>
      | "("; t = ctyp; "*"; tl = LIST1 ctyp SEP "*"; ")" → mktuptyp loc t tl
      | "("; t = ctyp; ")" → <:ctyp< $t$ >>
      | "["; cdl = V (LIST1 constructor_declaration SEP "|"); "]" →
          <:ctyp< [ $_list:cdl$ ] >>
      | "["; "|"; "]" →
          <:ctyp< [ $list:[]$ ] >>
      | "{"; ldl = V (LIST1 label_declaration SEP ";"); "}" →
          <:ctyp< { $_list:ldl$ } >> ] ]
  ;
  ctyp_below_alg_attribute:
  [ [ x = ctyp LEVEL "below_alg_attribute" -> x ]
  ]
  ;
  cons_ident:
  [ [ ci = V UIDENT "uid" "" -> ci
    | "[" ; "]" -> <:vala< "[]" >>
    | "(" ; ")" -> <:vala< "()" >>
    | "(" ; "::" ; ")" -> <:vala< "::" >>
    ] ] ;
  constructor_declaration:
    [ [ ci = cons_ident; (ls, tl,rto,attrs) = rest_constructor_declaration →
          <:constructor< $_uid:ci$ of $_list:ls$ . $_list:tl$ $_rto:rto$ $_algattrs:attrs$ >>
      ] ]
  ;
  rest_constructor_declaration:
    [ [ "of"; ls = type_binder_opt ; cal = V (GREEDY LIST1 ctyp_below_alg_attribute SEP "and") ;
        rto = V (OPT [ ":"; t = ctyp_below_alg_attribute -> t ]) "rto" ; attrs = alg_attributes →
          (ls, cal, rto, attrs)
      | rto = V (OPT [ ":"; t = ctyp_below_alg_attribute -> t ]) "rto" ; attrs = alg_attributes →
          (<:vala< [] >>, <:vala< [] >>, rto, attrs)
      ] ]
  ;
  extension_constructor:
  [ [ ci = cons_ident ; "="; b = V longident "longid" ; alg_attrs = alg_attributes ->
        <:extension_constructor< $_uid:ci$ = $_longid:b$ $_algattrs:alg_attrs$ >>
    | ci = cons_ident; (ls, tl,rto,attrs) = rest_constructor_declaration →
        <:extension_constructor< $_uid:ci$ of $_list:ls$ . $_list:tl$ $_rto:rto$ $_algattrs:attrs$ >>
    ] ]
  ;

  label_declaration:
    [ [ i = LIDENT; ":"; mf = FLAG "mutable"; t = ctyp LEVEL "below_alg_attribute" ; attrs = alg_attributes →
          mklabdecl loc i mf t attrs ] ]
  ;
  ident:
    [ [ i = LIDENT → mkident i
      | i = UIDENT → mkident i ] ]
  ;
  direction_flag:
    [ [ "to" → True
      | "downto" → False ] ]
  ;
  typevar:
    [ [ "'"; i = ident → i 
      | i = GIDENT -> greek_ascii_equiv i
      ] ]
  ;
  (* Objects and Classes *)
  str_item: AFTER "top"
    [ [ "class"; cd = V (LIST1 class_declaration SEP "and") →
          <:str_item< class $_list:cd$ >>
      | "class"; "type";
        ctd = V (LIST1 class_type_declaration SEP "and") →
          <:str_item< class type $_list:ctd$ >>
      | x = NEXT -> x
      ] ]
  ;
  sig_item: AFTER "top"
    [ [ "class"; cd = V (LIST1 class_description SEP "and") →
          <:sig_item< class $_list:cd$ >>
      | "class"; "type"; ctd = V (LIST1 class_type_declaration SEP "and") →
          <:sig_item< class type $_list:ctd$ >>
      | x = NEXT -> x
      ] ]
  ;
  class_declaration:
    [ [ vf = V (FLAG "virtual"); i = V LIDENT; ctp = class_type_parameters;
        cfb = class_fun_binding ; attrs = item_attributes →
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = i; MLast.ciExp = cfb; MLast.ciAttributes = attrs} ] ]
  ;
  class_fun_binding:
    [ [ "="; ce = class_expr → ce
      | ":"; ct = class_type; "="; ce = class_expr →
          <:class_expr< ($ce$ : $ct$) >>
      | p = ipatt; cfb = SELF → <:class_expr< fun $p$ → $cfb$ >> ] ]
  ;
  class_type_parameters:
    [ [ → (loc, <:vala< [] >>)
      | "["; tpl = V (LIST1 type_parameter SEP ","); "]" → (loc, tpl) ] ]
  ;
  class_fun_def:
    [ [ p = ipatt; ce = SELF → <:class_expr< fun $p$ → $ce$ >>
      | "->"; ce = class_expr → ce ] ]
  ;
  class_expr:
    [ "top"
      [ "fun"; alg_attrs = alg_attributes_no_anti; p = ipatt; ce = class_fun_def →
          class_expr_wrap_attrs loc <:class_expr< fun $p$ → $ce$ >> alg_attrs
      | "let"; rf = V (FLAG "rec"); lb = V (LIST1 let_binding SEP "and");
        "in"; ce = SELF →
          <:class_expr< let $_flag:rf$ $_list:lb$ in $ce$ >>
      | "let"; "open"; ovf = V (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
          <:class_expr< let open $_!:ovf$ $longid:i$ in $ce$ >>
      | x = NEXT -> x
      ]
    | "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:class_expr< $ct$ [@ $_attribute:attr$ ] >>
      ]
    | [ e = alg_extension -> <:class_expr< [% $_extension:e$ ] >>
      | x = NEXT -> x
      ]
    | [ ce = class_expr_apply -> ce ]
    ]
    ;
  class_expr_apply:
    [ "apply" LEFTA
      [ ce = SELF; e = expr LEVEL "label" →
          <:class_expr< $ce$ $exp:e$ >> ]
    | [ ce = class_expr_simple -> ce ]
    ]
    ;
  class_expr_simple:
    [ "simple"
      [ cli = V longident_lident "lilongid" →
          <:class_expr< $_lilongid:cli$ >>
      | "object"; cspo = V (OPT class_self_patt); cf = class_structure;
        "end" →
          <:class_expr< object $_opt:cspo$ $_list:cf$ end >>
      | "["; ctcl = V (LIST1 ctyp SEP ","); "]";
        cli = V longident_lident "lilongid" →
          <:class_expr< [ $_list:ctcl$ ] $_lilongid:cli$ >>
      | "("; ce = class_expr; ":"; ct = class_type; ")" →
          <:class_expr< ($ce$ : $ct$) >>
      | "("; ce = class_expr; ")" → ce
      ] ]
  ;
  class_structure:
    [ [ cf = V (LIST0 [ ci = class_str_item; ";" → ci ]) → cf ] ]
  ;
  class_self_patt:
    [ [ "("; p = patt; ")" → p
      | "("; p = patt; ":"; t = ctyp; ")" → <:patt< ($p$ : $t$) >> ] ]
  ;
  class_str_item:
    [ [ "declare"; st = V (LIST0 [ s= class_str_item; ";" → s ]); "end" →
          <:class_str_item< declare $_list:st$ end >>
      | "inherit"; ovf = V (FLAG "!") "!"; ce = class_expr; pb = V (OPT as_lident) ; attrs = item_attributes →
          <:class_str_item< inherit $_!:ovf$ $ce$ $_opt:pb$ $_itemattrs:attrs$ >>
      | "value"; ovf = V (FLAG "!") "!"; mf = V (FLAG "mutable");
        lab = V lident "lid" ""; e = cvalue_binding ; attrs = item_attributes →
          <:class_str_item< value $_!:ovf$ $_flag:mf$ $_lid:lab$ = $e$ $_itemattrs:attrs$ >>
      | "value"; "virtual"; mf = V (FLAG "mutable");
        lab = V lident "lid" ""; ":"; t = ctyp ; attrs = item_attributes →
          <:class_str_item< value virtual $_flag:mf$ $_lid:lab$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; pf = V (FLAG "private"); l = V lident "lid" "";
        ":"; t = ctyp ; attrs = item_attributes →
          <:class_str_item< method virtual $_flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; ovf = V (FLAG "!") "!"; pf = V (FLAG "private") "priv";
        l = V lident "lid" ""; topt = V (GREEDY OPT polyt); e = fun_binding ; attrs = item_attributes →
          <:class_str_item<
            method $_!:ovf$ $_priv:pf$ $_lid:l$ $_opt:topt$ = $e$ $_itemattrs:attrs$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes →
          <:class_str_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | "initializer"; se = expr ; attrs = item_attributes → <:class_str_item< initializer $se$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_str_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_str_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  as_lident:
    [ [ "as"; i = LIDENT → mkident i ] ]
  ;
  polyt:
    [ [ ":"; t = ctyp → t ] ]
  ;
  cvalue_binding:
    [ [ "="; e = expr → e
      | ":"; t = ctyp; "="; e = expr → <:expr< ($e$ : $t$) >>
      | ":"; t = ctyp; ":>"; t2 = ctyp; "="; e = expr →
          <:expr< ($e$ : $t$ :> $t2$) >>
      | ":>"; t = ctyp; "="; e = expr → <:expr< ($e$ :> $t$) >> ] ]
  ;
  lident:
    [ [ i = LIDENT → mkident i ] ]
  ;
  class_type:
    [ "top" RIGHTA
      [ "["; t = ctyp; "]"; "->"; ct = SELF →
          <:class_type< [ $t$ ] → $ct$ >>
      | "let"; "open"; ovf = V (FLAG "!") "!"; i = extended_longident; "in"; ce = SELF →
          <:class_type< let open $_!:ovf$ $longid:i$ in $ce$ >>
      ]
    | "alg_attribute" LEFTA
      [ ct = SELF ; "[@" ; attr = V attribute_body "attribute"; "]" ->
        <:class_type< $ct$ [@ $_attribute:attr$ ] >>
      ]

    | LEFTA [ ct = SELF; "["; tl = V (LIST1 ctyp SEP ","); "]" →
          <:class_type< $ct$ [ $_list:tl$ ] >> ]
    | [ "object"; cst = V (OPT class_self_type);
        csf = V (LIST0 [ csi = class_sig_item; ";" → csi ]); "end" →
          <:class_type< object $_opt:cst$ $_list:csf$ end >>
      | x = NEXT -> x
      ]
    | "simple"
      [ li = extended_longident; "."; i = V LIDENT → <:class_type< $longid:li$ . $_lid:i$ >>
      | i = V LIDENT → <:class_type< $_lid:i$ >>
      | "("; ct = class_type; ")" → ct
      | e = alg_extension -> <:class_type< [% $_extension:e$ ] >>
 ] ]
  ;
  class_self_type:
    [ [ "("; t = ctyp; ")" → t ] ]
  ;
  class_sig_item:
    [ [ "declare"; st = V (LIST0 [ s = class_sig_item; ";" → s ]); "end" →
          <:class_sig_item< declare $_list:st$ end >>
      | "inherit"; cs = class_type ; attrs = item_attributes →
          <:class_sig_item< inherit $cs$ $_itemattrs:attrs$ >>
      | "value"; mf = V (GREEDY FLAG "mutable") "mflag"; vf = V (GREEDY FLAG "virtual") "vflag"; l = V lident "lid" ""; ":";
        t = ctyp ; attrs = item_attributes →
          <:class_sig_item< value $_flag:mf$ $_flag:vf$  $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; "virtual"; pf = V (FLAG "private"); l = V lident "lid" "";
        ":"; t = ctyp ; attrs = item_attributes →
          <:class_sig_item< method virtual $_flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "method"; pf = V (FLAG "private"); l = V lident "lid" ""; ":";
        t = ctyp ; attrs = item_attributes →
          <:class_sig_item< method $_flag:pf$ $_lid:l$ : $t$ $_itemattrs:attrs$ >>
      | "type"; t1 = ctyp; "="; t2 = ctyp ; attrs = item_attributes →
          <:class_sig_item< type $t1$ = $t2$ $_itemattrs:attrs$ >>
      | attr = floating_attribute -> <:class_sig_item< [@@@ $_attribute:attr$ ] >>
      | e = item_extension -> <:class_sig_item< [%% $_extension:e$ ] >>
      ] ]
  ;
  class_description:
    [ [ vf = V (FLAG "virtual"); n = V LIDENT; ctp = class_type_parameters;
        ":"; ct = class_type ; attrs = item_attributes →
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = ct; MLast.ciAttributes = attrs} ] ]
  ;
  class_type_declaration:
    [ [ vf = V (FLAG "virtual"); n = V LIDENT; ctp = class_type_parameters;
        "="; cs = class_type ; attrs = item_attributes →
          {MLast.ciLoc = loc; MLast.ciVir = vf; MLast.ciPrm = ctp;
           MLast.ciNam = n; MLast.ciExp = cs; MLast.ciAttributes = attrs} ] ]
  ;
  expr: AFTER "apply"
    [ NONA
      [ "new"; (ext,attrs) = ext_attributes; cli = V longident_lident "lilongid" → 
          expr_to_inline <:expr< new $_lilongid:cli$ >> ext attrs
      | "object"; (ext,attrs) = ext_attributes; cspo = V (OPT class_self_patt); cf = class_structure;
        "end" →
          expr_to_inline <:expr< object $_opt:cspo$ $_list:cf$ end >> ext attrs
      | e = NEXT -> e
      ] ]
  ;
  expr: LEVEL "."
    [ [ e = SELF; "#"; lab = V lident "lid" "" →
          <:expr< $e$ # $_lid:lab$ >>
      | e = SELF; op = HASHOP ; e2 = SELF -> <:expr< $lid:op$ $e$ $e2$ >>
      ] ]
  ;
  expr: LEVEL "simple"
    [ [ "("; e = expr; ":"; t = ctyp; ":>"; t2 = ctyp; ")" →
          <:expr< ($e$ : $t$ :> $t2$ ) >>
      | "("; e = expr; ":>"; t = ctyp; ")" → <:expr< ($e$ :> $t$) >>
      | "{<"; fel = V (LIST0 field_expr SEP ";"); ">}" →
          <:expr< {< $_list:fel$ >} >> ] ]
  ;
  field_expr:
    [ [ l = lident; "="; e = expr → (l, e) ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "#"; cli = V extended_longident_lident "lilongid" → <:ctyp< # $_lilongid:cli$ >>

      | "<"; ml = V (GREEDY LIST0 field SEP ";"); v = V (FLAG ".."); ">" →
          <:ctyp< < $_list:ml$ $_flag:v$ > >> ] ]
  ;
  field:
    [ [ check_lident_colon ; lab = LIDENT; ":"; t = ctyp_below_alg_attribute; alg_attrs = alg_attributes →
        (Some (mkident lab), t, alg_attrs)
      | t = ctyp_below_alg_attribute; alg_attrs = alg_attributes ->
        (None, t, alg_attrs)
      ] ]
  ;
  longident_lident:
    [ [ li = V longident "longid" ; "."; i = V LIDENT → (Some li, i)
      | i = V LIDENT → (None, i)
      ] ]
  ;
  extended_longident_lident:
    [ [ li = V extended_longident "longid" ; "."; i = V LIDENT → (Some li, i)
      | i = V LIDENT → (None, i)
      ] ]
  ;
  (* Labels *)
  ctyp: AFTER "arrow"
    [ NONA
      [ i = V TILDEIDENTCOLON; t = SELF → <:ctyp< ~$_:i$: $t$ >>
      | i = V QUESTIONIDENTCOLON; t = SELF → <:ctyp< ?$_:i$: $t$ >>
      | x = NEXT -> x
      ] ]
  ;
  ctyp: LEVEL "simple"
    [ [ "["; "="; rfl = poly_variant_list; "]" →
          <:ctyp< [ = $_list:rfl$ ] >>
      | "["; ">"; rfl = poly_variant_list; "]" →
          <:ctyp< [ > $_list:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; "]" →
          <:ctyp< [ < $_list:rfl$ ] >>
      | "["; "<"; rfl = poly_variant_list; ">"; ntl = V (LIST1 name_tag);
        "]" →
          <:ctyp< [ < $_list:rfl$ > $_list:ntl$ ] >> ] ]
  ;
  poly_variant_list:
    [ [ rfl = V (LIST0 poly_variant SEP "|") → rfl ] ]
  ;
  poly_variant:
    [ [ "`"; i = V ident "" ; attrs = alg_attributes → <:poly_variant< ` $_:i$ $_algattrs:attrs$ >>
      | "`"; i = V ident ""; "of"; ao = V (FLAG "&");
        l = V (LIST1 ctyp_below_alg_attribute SEP "&") ; attrs = alg_attributes →
          <:poly_variant< ` $_:i$ of $_flag:ao$ $_list:l$ $_algattrs:attrs$ >>
      | t = ctyp → <:poly_variant< $t$ >> ] ]
  ;
  name_tag:
    [ [ "`"; i = ident → i ] ]
  ;
  patt: LEVEL "simple"
    [ [ "`"; s = V ident "" → <:patt< ` $_:s$ >>
      | "#"; lili = V extended_longident_lident "lilongid" → <:patt< # $_lilongid:lili$ >>
      | "~"; "{"; lppo = V (LIST1 patt_tcon_opt_eq_patt SEP ";"); "}" →
          <:patt< ~{$_list:lppo$} >>
      | check_question_lbrace ; "?"; "{"; p = patt_tcon; eo = V (OPT [ "="; e = expr → e ]); "}" →
          <:patt< ?{$p$ $_opt:eo$ } >>
      | i = V TILDEIDENTCOLON; p = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$ = $p$} >>
      | i = V TILDEIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$} >>
      | p = patt_option_label →
          let _ = warning_deprecated_since_6_00 loc in
          p ] ]
  ;
  patt_tcon_opt_eq_patt:
    [ [ p = patt_tcon; po = V (OPT [ "="; p' = patt → p' ]) → (p, po) ] ]
  ;
  patt_tcon:
    [ [ p = patt → p
      | p = patt; ":"; t = ctyp → <:patt< ($p$ : $t$) >> ] ]
  ;
  ipatt: AFTER "simple"
    [ [ "~"; "{"; lppo = V (LIST1 ipatt_tcon_opt_eq_patt SEP ";"); "}" →
          <:patt< ~{$_list:lppo$} >>
      | check_question_lbrace ; "?"; "{"; p = ipatt_tcon; eo = V (OPT [ "="; e = expr → e ]); "}" →
          <:patt< ?{$p$ $_opt:eo$ } >>

      | i = V TILDEIDENTCOLON; p = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$ = $p$} >>
      | i = V TILDEIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:patt< ~{$_lid:i$} >>
      | p = patt_option_label →
          let _ = warning_deprecated_since_6_00 loc in
          p
      ] ]
  ;
  ipatt_tcon_opt_eq_patt:
    [ [ p = ipatt_tcon; po = V (OPT [ "="; p' = patt → p' ]) → (p, po) ] ]
  ;
  ipatt_tcon:
    [ [ p = ipatt → p
      | p = ipatt; PRIORITY 1 ; ":"; t = ctyp → <:patt< ($p$ : $t$) >> ] ]
  ;
  patt_option_label:
    [ [ i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; ":"; t = ctyp; "=";
        e = expr; ")" →
          <:patt< ?{$_lid:i$ : $t$ = ?{$_lid:j$ = $e$}} >>
      | i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; ":"; t = ctyp; ")" →
          <:patt< ?{$_lid:i$ : $t$ = ?{$_lid:j$}} >>
      | i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; "="; e = expr; ")" →
          <:patt< ?{$_lid:i$ = ?{$_lid:j$ = $e$}} >>
      | i = V QUESTIONIDENTCOLON; "("; j = V LIDENT; ")" →
          <:patt< ?{$_lid:i$ = $_lid:j$} >>
      | i = V QUESTIONIDENT →
          <:patt< ?{$_lid:i$} >>
      | "?"; "("; i = V LIDENT; ":"; t = ctyp; "="; e = expr; ")" →
          <:patt< ?{$_lid:i$ : $t$ = $e$} >>
      | "?"; "("; i = V LIDENT; ":"; t = ctyp; ")" →
          <:patt< ?{$_lid:i$ : $t$} >>
      | "?"; "("; i = V LIDENT; "="; e = expr; ")" →
          <:patt< ?{$_lid:i$ = $e$} >>
      | "?"; "("; i = V LIDENT; ")" →
          <:patt< ?{$_lid:i$} >> ] ]
  ;
  expr: AFTER "apply"
    [ "label" NONA
      [ "~"; "{"; lpeo = V (LIST1 ipatt_tcon_fun_binding SEP ";"); "}" →
          <:expr< ~{$_list:lpeo$ } >>
      | "?"; "{"; p = ipatt_tcon; eo = V (OPT fun_binding); "}" →
          <:expr< ?{$p$ $_opt:eo$ } >>
      | i = V TILDEIDENTCOLON; e = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ~{$_lid:i$ = $e$} >>
      | i = V TILDEIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ~{$_lid:i$} >>
      | i = V QUESTIONIDENTCOLON; e = SELF →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ?{$_lid:i$ = $e$} >>
      | i = V QUESTIONIDENT →
          let _ = warning_deprecated_since_6_00 loc in
          <:expr< ?{$_lid:i$} >>
      | x = NEXT -> x
      ] ]
  ;
  ipatt_tcon_fun_binding:
    [ [ p = ipatt_tcon; eo = V (OPT fun_binding) → (p, eo) ] ]
  ;
  expr: LEVEL "simple"
    [ [ "`"; s = V ident "" → <:expr< ` $_:s$ >> ] ]
  ;

  interf:
    [ [ "#"; n = V LIDENT; dp = OPT expr; ";" →
          ([(<:sig_item< # $_lid:n$ $opt:dp$ >>, loc)], None)
      | si = sig_item_semi; (sil, stopped) = SELF →
          ([si :: sil], stopped)
      | EOI →
          ([], Some loc) ] ]
  ;
  sig_item_semi:
    [ [ si = sig_item; ";" → (si, loc) ] ]
  ;
  implem:
    [ [ check_hash_v_lident ; "#"; n = V LIDENT; dp = OPT expr; ";" →
          ([(<:str_item< # $_lid:n$ $opt:dp$ >>, loc)], None)
      | si = str_item_semi; (sil, stopped) = SELF →
          ([si :: sil], stopped)
      | EOI →
          ([], Some loc) ] ]
  ;
  str_item_semi:
    [ [ si = str_item; ";" → (si, loc) ] ]
  ;
  top_phrase:
    [ [ ph = phrase → Some ph
      | EOI → None ] ]
  ;
  use_file:
    [ [ check_hash_lident ; "#"; n = LIDENT; dp = OPT expr; ";" →
          ([<:str_item< # $lid:n$ $opt:dp$ >>], True)
      | si = str_item; ";"; (sil, stopped) = SELF → ([si :: sil], stopped)
      | EOI → ([], False) ] ]
  ;
  phrase:
    [ [ check_hash_lident ; "#"; n = LIDENT; dp = OPT expr; ";" →
          <:str_item< # $lid:n$ $opt:dp$ >>
      | sti = str_item; ";" → sti ] ]
  ;
  expr: LEVEL "simple"
    [ [ x = QUOTATION →
          let con = quotation_content x in
          Pcaml.handle_expr_quotation loc con ] ]
  ;
  patt: LEVEL "simple"
    [ [ x = QUOTATION →
          let con = quotation_content x in
          Pcaml.handle_patt_quotation loc con ] ]
  ;
END ;
|foo} ;
];

value pa e s = s |> Stream.of_string |> Grammar.Entry.parse e ;
