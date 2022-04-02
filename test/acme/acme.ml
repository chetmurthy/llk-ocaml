(* camlp5r *)
(* acme.ml,v *)

value input_file = ref "" ;
value nonws_re = Pcre.regexp "\\S" ;
value has_nonws s = Pcre.pmatch ~{rex=nonws_re} s;

value lexer = Plexing.lexer_func_of_ocamllex_located Acmelexer.token ;
value lexer = {Plexing.tok_func = lexer;
 Plexing.tok_using _ = (); Plexing.tok_removing _ = ();
 Plexing.tok_match = Plexing.default_match;
 Plexing.tok_text = Plexing.lexer_text;
 Plexing.tok_comm = None} ;

value g = Grammar.gcreate lexer;

value loc_strip_comment loc = Ploc.with_comment loc "" ;

[@@@llk
{foo|
GRAMMAR Acme:
  EXTEND g ;
  
    EXPORT: acmeCompUnit_eoi acmeCompUnit acmeImportDeclaration stringLiteral filename identifier codeLiteral
      acmeFamilyDeclaration acmeFamilyBody acmeSystemDeclaration acmeSystemBody
      acmeDesignDeclaration acmeComponentTypeRef acmeComponentInstantiatedTypeRef
      acmeConnectorTypeRef acmeConnectorInstantiatedTypeRef acmePortTypeRef
      acmePortInstantiatedTypeRef acmeGroupTypeRef acmeGroupInstantiatedTypeRef acmeRoleTypeRef
      acmeRoleInstantiatedTypeRef acmeViewTypeRef acmeViewInstantiatedTypeRef acmeFamilyRef
      acmeFamilyInstantiationRef acmeElementTypeRef acmePropertyTypeDeclarationRef acmeInstanceRef
      acmeGenericElementTypeDeclaration acmeGenericElementBody acmeGroupTypeDeclaration
      acmeGroupDeclaration acmeGroupBody acmeMembersBlock acmePortTypeDeclaration
      acmePortDeclaration acmePortBody acmeRoleTypeDeclaration acmeRoleDeclaration acmeRoleBody
      acmeComponentTypeDeclaration acmeComponentDeclaration acmeComponentBody
      acmeConnectorTypeDeclaration acmeConnectorDeclaration acmeConnectorBody
      acmeRepresentationDeclaration acmeBindingsMapDeclaration acmeBindingDeclaration
      acmeAttachmentDeclaration acmePropertyDeclaration acmePropertyValueDeclaration enumidentifier
      acmePropertyElement acmePropertyCompoundElement acmePropertySet acmePropertyRecordEntry
      acmePropertyRecord acmePropertySequence acmePropertyTypeRecord acmePropertyTypeSet
      acmePropertyTypeSequence acmePropertyTypeEnum acmePropertyRecordFieldDescription
      acmePropertyTypeRef acmePropertyTypeStructure acmePropertyTypeDeclaration
      acmePropertyBlockEntry acmePropertyBlock acmePropertyTypeInt acmePropertyTypeAny
      acmePropertyTypeFloat acmePropertyTypeDouble acmePropertyTypeString acmePropertyTypeBoolean
      acmeViewDeclaration acmeViewTypeDeclaration acmeViewBody designRule
      acmeDesignAnalysisDeclaration formalParam terminatedDesignRuleExpression designRuleExpression
      aSTDRImpliesExpression dRIffExpression dRAndExpression dRNegateExpression dREqualityExpression
      dRRelationalExpression dRAdditiveExpression dRMultiplicativeExpression dRNegativeExpression
      primitiveExpression parentheticalExpression reference setReference actualParams
      literalConstant quantifiedExpression distinctVariableSetDeclaration variableSetDeclaration
      sequenceExpression setExpression pathExpression pathExpressionContinuation literalSet
      literalSequence literalRecordEntry literalRecord setConstructor acmeTypeRef;
    
    acmeCompUnit_eoi: [ [ x = acmeCompUnit ; EOI -> x ] ] ;
    
    acmeCompUnit:
      
      [ [ GREEDY LIST0 acmeImportDeclaration;
          GREEDY LIST1 [ acmeSystemDeclaration | acmeFamilyDeclaration | acmeDesignDeclaration ] ] ]
    ;
    acmeImportDeclaration:
      
      [ [ "import"; [ filename | stringLiteral ]; ";" ] ]
    ;
    stringLiteral:
      
      [ [ STRING_LITERAL ] ]
    ;
    filename:
      
      [ [ GREEDY OPT [ "$" | "%" ]; IDENTIFIER;
          GREEDY LIST0
            [ GREEDY LIST1 [ "." | ":" | "-" | "+" | "\\" | "\\\\" | "/" | "$" | "%" ]; IDENTIFIER ] ] ]
    ;
    identifier:
      
      [ [ IDENTIFIER ] ]
    ;
    codeLiteral:
      
      [ [ STRING_LITERAL ] ]
    ;
    acmeFamilyDeclaration:
      
      [ [ [ "family" | "style" ]; identifier;
          [ ";" -> ()
          | "="; acmeFamilyBody; GREEDY OPT ";"
          | "extends"; acmeFamilyRef; GREEDY LIST0 [ ","; acmeFamilyRef ];
            [ ";" -> () | "with"; acmeFamilyBody; GREEDY OPT ";" ] ] ] ]
    ;
    acmeFamilyBody:
      
      [ [ "{";
          GREEDY LIST0
            [ GREEDY OPT [ "public" | "private" ]; GREEDY OPT [ "final" | "abstract" ];
              [ acmePortTypeDeclaration
              | acmeRoleTypeDeclaration
              | acmeComponentTypeDeclaration
              | acmeConnectorTypeDeclaration
              | acmeGenericElementTypeDeclaration
              | acmePropertyTypeDeclaration
              | acmeGroupTypeDeclaration ]
            | [ acmeDesignAnalysisDeclaration
              | designRule
              | acmePortDeclaration
              | acmeRoleDeclaration
              | acmeComponentDeclaration
              | acmeConnectorDeclaration
              | acmePropertyDeclaration
              | acmeGroupDeclaration
              | acmeAttachmentDeclaration ] ];
          "}" ] ]
    ;
    acmeSystemDeclaration:
      
      [ [ "system"; identifier; GREEDY OPT [ ":"; GREEDY LIST1 acmeFamilyRef SEP "," ];
          [ ";" -> ()
          | "=";
            [ acmeSystemBody; GREEDY OPT ";"
            | "new"; acmeFamilyInstantiationRef; GREEDY LIST0 [ ","; acmeFamilyInstantiationRef ];
              [ ";" -> () | "extended"; "with"; acmeSystemBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeSystemBody:
      
      [ [ "{";
          GREEDY LIST0
            [ acmePropertyDeclaration
            | acmeComponentDeclaration
            | acmeConnectorDeclaration
            | acmeAttachmentDeclaration
            | acmeGroupDeclaration
            | designRule ];
          "}" ] ]
    ;
    acmeDesignDeclaration:
      
      [ [ "design" ] ]
    ;
    acmeComponentTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeComponentInstantiatedTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeConnectorTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeConnectorInstantiatedTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmePortTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmePortInstantiatedTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeGroupTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeGroupInstantiatedTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeRoleTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeRoleInstantiatedTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeViewTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeViewInstantiatedTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeFamilyRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeFamilyInstantiationRef:
      
      [ [ identifier ] ]
    ;
    acmeElementTypeRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmePropertyTypeDeclarationRef:
      
      [ [ identifier; GREEDY OPT [ "."; identifier ] ] ]
    ;
    acmeInstanceRef:
      
      [ [ GREEDY LIST1 IDENTIFIER SEP "." ] ]
    ;
    acmeGenericElementTypeDeclaration:
      
      [ [ "element"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmeGenericElementBody; GREEDY OPT ";"
            | "extends"; acmeElementTypeRef; GREEDY LIST0 [ ","; acmeElementTypeRef ];
              [ ";" -> () | "with"; acmeGenericElementBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeGenericElementBody:
      
      [ [ "{"; GREEDY LIST0 [ acmePropertyDeclaration | designRule ]; "}" ] ]
    ;
    acmeGroupTypeDeclaration:
      
      [ [ "group"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmeGroupBody; GREEDY OPT ";"
            | "extends"; acmeGroupTypeRef; GREEDY LIST0 [ ","; acmeGroupTypeRef ];
              [ ";" -> () | "with"; acmeGroupBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeGroupDeclaration:
      
      [ [ "group"; identifier; GREEDY OPT [ ":"; GREEDY LIST1 acmeGroupTypeRef SEP "," ];
          [ ";" -> ()
          | "=";
            [ acmeGroupBody; GREEDY OPT ";"
            | "new"; acmeGroupInstantiatedTypeRef;
              GREEDY LIST0 [ ","; acmeGroupInstantiatedTypeRef ];
              [ ";" -> () | "extended"; "with"; acmeGroupBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeGroupBody:
      
      [ [ "{"; GREEDY LIST0 [ acmeMembersBlock | acmePropertyDeclaration | designRule ]; "}" ] ]
    ;
    acmeMembersBlock:
      
      [ [ "members"; "{"; GREEDY OPT [ GREEDY LIST1 acmeInstanceRef SEP "," ]; "}"; GREEDY OPT ";" ] ]
    ;
    acmePortTypeDeclaration:
      
      [ [ "port"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmePortBody; GREEDY OPT ";"
            | "extends"; acmePortTypeRef; GREEDY LIST0 [ ","; acmePortTypeRef ];
              [ ";" -> () | "with"; acmePortBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmePortDeclaration:
      
      [ [ "port"; identifier; GREEDY OPT [ ":"; GREEDY LIST1 acmePortTypeRef SEP "," ];
          [ GREEDY OPT ";"
          | "=" ;
            [ acmePortBody; GREEDY OPT ";"
            | "new"; acmePortInstantiatedTypeRef; GREEDY LIST0 [ ","; acmePortInstantiatedTypeRef ];
              [ ";" -> () | "extended"; "with"; acmePortBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmePortBody:
      
      [ [ "{"; GREEDY LIST0 [ acmePropertyDeclaration | designRule | acmeRepresentationDeclaration ]; "}" ] ]
    ;
    acmeRoleTypeDeclaration:
      
      [ [ "role"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmeRoleBody; GREEDY OPT ";"
            | "extends"; acmeRoleTypeRef; GREEDY LIST0 [ ","; acmeRoleTypeRef ];
              [ ";" -> () | "with"; acmeRoleBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeRoleDeclaration:
      
      [ [ "role"; identifier; GREEDY OPT [ ":"; GREEDY LIST1 acmeRoleTypeRef SEP "," ];
          [ ";" -> ()
          | "=";
            [ acmeRoleBody; GREEDY OPT ";"
            | "new"; acmeRoleInstantiatedTypeRef; GREEDY LIST0 [ ","; acmeRoleInstantiatedTypeRef ];
              [ ";" -> () | "extended"; "with"; acmeRoleBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeRoleBody:
      
      [ [ "{"; GREEDY LIST0 [ acmePropertyDeclaration | designRule | acmeRepresentationDeclaration ]; "}" ] ]
    ;
    acmeComponentTypeDeclaration:
      
      [ [ "component"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmeComponentBody; GREEDY OPT ";"
            | "extends"; acmeComponentTypeRef; GREEDY LIST0 [ ","; acmeComponentTypeRef ];
              [ ";" -> () | "with"; acmeComponentBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeComponentDeclaration:
      
      [ [ "component"; identifier; GREEDY OPT [ ":"; GREEDY LIST1 acmeComponentTypeRef SEP "," ];
          [ ";" -> ()
          | "=";
            [ acmeComponentBody; GREEDY OPT ";"
            | "new"; acmeComponentInstantiatedTypeRef;
              GREEDY LIST0 [ ","; acmeComponentInstantiatedTypeRef ];
              [ ";" -> () | "extended"; "with"; acmeComponentBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeComponentBody:
      
      [ [ "{";
          GREEDY LIST0
            [ acmePropertyDeclaration
            | acmePortDeclaration
            | designRule
            | acmeRepresentationDeclaration ];
          "}" ] ]
    ;
    acmeConnectorTypeDeclaration:
      
      [ [ "connector"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmeConnectorBody; GREEDY OPT ";"
            | "extends"; acmeConnectorTypeRef; GREEDY LIST0 [ ","; acmeConnectorTypeRef ];
              [ ";" -> () | "with"; acmeConnectorBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeConnectorDeclaration:
      
      [ [ "connector"; identifier; GREEDY OPT [ ":"; GREEDY LIST1 acmeConnectorTypeRef SEP "," ];
          [ ";" -> ()
          | "=";
            [ acmeConnectorBody; GREEDY OPT ";"
            | "new"; acmeConnectorInstantiatedTypeRef;
              GREEDY LIST0 [ ","; acmeConnectorInstantiatedTypeRef ];
              [ ";" -> () | "extended"; "with"; acmeConnectorBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeConnectorBody:
      
      [ [ "{";
          GREEDY LIST0
            [ acmePropertyDeclaration
            | acmeRoleDeclaration
            | designRule
            | acmeRepresentationDeclaration ];
          "}" ] ]
    ;
    acmeRepresentationDeclaration:
      
      [ [ "representation"; GREEDY OPT [ IDENTIFIER; "=" ]; "{"; acmeSystemDeclaration;
          GREEDY OPT acmeBindingsMapDeclaration; "}"; GREEDY OPT ";" ] ]
    ;
    acmeBindingsMapDeclaration:
      
      [ [ "bindings"; "{"; GREEDY LIST0 acmeBindingDeclaration; "}"; GREEDY OPT ";" ] ]
    ;
    acmeBindingDeclaration:
      
      [ [ acmeInstanceRef; "to"; acmeInstanceRef;
          GREEDY OPT [ "{"; acmePropertyDeclaration; acmePropertyBlock; "}" ]; ";" ] ]
    ;
    acmeAttachmentDeclaration:
      
      [ [ "attachment"; acmeInstanceRef; "to"; acmeInstanceRef; ";" ] ]
    ;
    acmePropertyDeclaration:
      
      [ [ "property"; identifier; GREEDY OPT [ ":"; acmePropertyTypeRef ];
          GREEDY OPT
            [ "="; acmePropertyValueDeclaration | "containassign"; acmePropertyValueDeclaration ];
          GREEDY OPT acmePropertyBlock; ";" ] ]
    ;
    acmePropertyValueDeclaration:
      
      [ [ INTEGER_LITERAL -> ()
        | FLOATING_POINT_LITERAL -> ()
        | STRING_LITERAL -> ()
        | BOOLEAN/"false" -> ()
        | BOOLEAN/"true" -> ()
        | acmePropertySet
        | acmePropertyRecord
        | acmePropertySequence
        | enumidentifier ] ]
    ;
    enumidentifier:
      
      [ [ IDENTIFIER ] ]
    ;
    acmePropertyElement:
      
      [ [ IDENTIFIER; GREEDY LIST0 [ "."; IDENTIFIER ]
        | acmePropertyCompoundElement ] ]
    ;
    acmePropertyCompoundElement:
      
      [ [ acmePropertySet
        | acmePropertyRecord
        | acmePropertySequence ] ]
    ;
    acmePropertySet:
      
      [ [ "{"; GREEDY OPT [ GREEDY LIST1 acmePropertyValueDeclaration SEP "," ]; "}" ] ]
    ;
    acmePropertyRecordEntry:
      
      [ [ identifier; GREEDY OPT [ ":"; acmePropertyTypeRef ]; "="; acmePropertyValueDeclaration ] ]
    ;
    acmePropertyRecord:
      
      [ [ "["; GREEDY OPT [ GREEDY LIST1 acmePropertyRecordEntry SEP ";"; GREEDY OPT ";" ]; "]" ] ]
    ;
    acmePropertySequence:
      
      [ [ "<"; GREEDY OPT [ GREEDY LIST1 acmePropertyValueDeclaration SEP "," ]; ">" ] ]
    ;
    acmePropertyTypeRecord:
      
      [ [ "record"; "["; GREEDY LIST0 acmePropertyRecordFieldDescription; "]" ] ]
    ;
    acmePropertyTypeSet:
      
      [ [ "set"; "{"; GREEDY OPT acmeTypeRef; "}" ] ]
    ;
    acmePropertyTypeSequence:
      
      [ [ "sequence"; "<"; GREEDY OPT acmePropertyTypeRef; ">" ] ]
    ;
    acmePropertyTypeEnum:
      
      [ [ "enum"; "{"; GREEDY LIST1 identifier SEP ","; "}" ] ]
    ;
    acmePropertyRecordFieldDescription:
      
      [ [ identifier; ":"; acmePropertyTypeRef; ";" ] ]
    ;
    acmePropertyTypeRef:
      
      [ [ acmePropertyTypeStructure
        | acmePropertyTypeDeclarationRef ] ]
    ;
    acmePropertyTypeStructure:
      
      [ [ acmePropertyTypeAny
        | acmePropertyTypeInt
        | acmePropertyTypeFloat
        | acmePropertyTypeDouble
        | acmePropertyTypeString
        | acmePropertyTypeBoolean
        | acmePropertyTypeRecord
        | acmePropertyTypeSet
        | acmePropertyTypeSequence
        | acmePropertyTypeEnum ] ]
    ;
    acmePropertyTypeDeclaration:
      
      [ [ "property"; "type"; identifier;
          [ ";" -> ()
          | "=";
            [ acmePropertyTypeInt
            | acmePropertyTypeFloat
            | acmePropertyTypeDouble
            | acmePropertyTypeString
            | acmePropertyTypeBoolean
            | acmePropertyTypeRecord
            | acmePropertyTypeSet
            | acmePropertyTypeSequence
            | acmePropertyTypeEnum
            | acmePropertyTypeAny ];
            ";" -> () ] ] ]
    ;
    acmePropertyBlockEntry:
      
      [ [ identifier; GREEDY OPT [ ":"; acmePropertyTypeRef ];
          GREEDY OPT
            [ "="; acmePropertyValueDeclaration | "containassign"; acmePropertyValueDeclaration ];
          ";" ] ]
    ;
    acmePropertyBlock:
      
      [ [ "<<"; GREEDY LIST1 acmePropertyBlockEntry; ">>" ] ]
    ;
    acmePropertyTypeInt:
      
      [ [ "int" ] ]
    ;
    acmePropertyTypeAny:
      
      [ [ "any" ] ]
    ;
    acmePropertyTypeFloat:
      
      [ [ "float" ] ]
    ;
    acmePropertyTypeDouble:
      
      [ [ "double" ] ]
    ;
    acmePropertyTypeString:
      
      [ [ "string" ] ]
    ;
    acmePropertyTypeBoolean:
      
      [ [ BOOLEAN ] ]
    ;
    acmeViewDeclaration:
      
      [ [ "view"; identifier; GREEDY OPT [ ":"; acmeViewTypeRef ];
          [ ";" -> ()
          | "=";
            [ acmeViewBody; GREEDY OPT ";"
            | "new"; acmeViewInstantiatedTypeRef;
              [ ";" -> () | "extended"; "with"; acmeViewBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeViewTypeDeclaration:
      
      [ [ "view"; "type"; identifier;
          [ ";" -> ()
          | [ "="; acmeViewBody; GREEDY OPT ";"
            | "extends"; acmeViewTypeRef; [ ";" -> () | "with"; acmeViewBody; GREEDY OPT ";" ] ] ] ] ]
    ;
    acmeViewBody:
      
      [ [ "{"; "}" ] ]
    ;
    designRule:
      
      [ [ GREEDY OPT "design"; GREEDY OPT [ "rule"; IDENTIFIER; GREEDY OPT "=" ];
          GREEDY OPT [ "invariant"; designRuleExpression | "heuristic"; designRuleExpression ];
          GREEDY OPT acmePropertyBlock; ";" ] ]
    ;
    acmeDesignAnalysisDeclaration:
      
      [ [ GREEDY OPT "design"; "analysis"; IDENTIFIER; "("; GREEDY OPT [ GREEDY LIST1 formalParam SEP "," ];
          ")"; ":"; acmeTypeRef; "="; designRuleExpression; GREEDY OPT acmePropertyBlock; ";"
        | "external"; GREEDY OPT "design"; "analysis"; IDENTIFIER; "(";
          GREEDY OPT [ GREEDY LIST1 formalParam SEP "," ]; ")"; ":"; acmeTypeRef; "=";
          [ codeLiteral | identifier; GREEDY LIST0 [ "."; identifier ] ]; ";" ] ]
    ;
    formalParam:
      
      [ [ identifier; ":"; acmeTypeRef ] ]
    ;
    terminatedDesignRuleExpression:
      
      [ [ designRuleExpression; ";" ] ]
    ;
    designRuleExpression:
      
      [ [ GREEDY LIST1 aSTDRImpliesExpression SEP "or" ] ]
    ;
    aSTDRImpliesExpression:
      
      [ [ GREEDY LIST1 dRIffExpression SEP "->" ] ]
    ;
    dRIffExpression:
      
      [ [ GREEDY LIST1 dRAndExpression SEP "<->" ] ]
    ;
    dRAndExpression:
      
      [ [ GREEDY LIST1 dRNegateExpression SEP "and" ] ]
    ;
    dRNegateExpression:
      
      [ [ "!"; dRNegateExpression
        | dREqualityExpression ] ]
    ;
    dREqualityExpression:
      
      [ [ dRRelationalExpression;
          GREEDY LIST0 [ "=="; dRRelationalExpression | "!="; dRRelationalExpression ] ] ]
    ;
    dRRelationalExpression:
      
      [ [ dRAdditiveExpression;
          GREEDY LIST0
            [ "<"; dRAdditiveExpression
            | ">"; dRAdditiveExpression
            | "<="; dRAdditiveExpression
            | ">="; dRAdditiveExpression ] ] ]
    ;
    dRAdditiveExpression:
      
      [ [ dRMultiplicativeExpression;
          GREEDY LIST0 [ "+"; dRMultiplicativeExpression | "-"; dRMultiplicativeExpression ] ] ]
    ;
    dRMultiplicativeExpression:
      
      [ [ dRNegativeExpression;
          GREEDY LIST0
            [ "*"; dRNegativeExpression
            | "/"; dRNegativeExpression
            | "%"; dRNegativeExpression
            | "power"; dRNegativeExpression ] ] ]
    ;
    dRNegativeExpression:
      
      [ [ "-"; dRNegativeExpression
        | primitiveExpression ] ]
    ;
    primitiveExpression:
      
      [ [ literalConstant
        | reference
        | parentheticalExpression
        | setExpression
        | literalSequence
        | literalRecord
        | quantifiedExpression
        | sequenceExpression ] ]
    ;
    parentheticalExpression:
      
      [ [ "("; designRuleExpression; ")" ] ]
    ;
    reference:
      
      [ [ identifier; GREEDY LIST0 [ "."; [ identifier | setReference ] ]; GREEDY OPT actualParams ] ]
    ;
    setReference:
      
      [ [ "type"
        | "components"
        | "connectors"
        | "ports"
        | "roles"
        | "groups"
        | "members"
        | "properties"
        | "representations"
        | "attachedports"
        | "attachedroles" ] ]
    ;
    actualParams:
      
      [ [ "("; GREEDY OPT [ GREEDY LIST1 designRuleExpression SEP "," ]; ")" ] ]
    ;
    literalConstant:
      
      [ [ INTEGER_LITERAL -> ()
        | FLOATING_POINT_LITERAL -> ()
        | STRING_LITERAL -> ()
        | BOOLEAN/"true" -> ()
        | BOOLEAN/"false" -> ()
        | "component" -> ()
        | "group" -> ()
        | "connector" -> ()
        | "port" -> ()
        | "role" -> ()
        | "system" -> ()
        | "element" -> ()
        | "property" -> ()
        | "int" -> ()
        | "float" -> ()
        | "double" -> ()
        | "string" -> ()
        | BOOLEAN -> ()
        | "enum" -> ()
        | "set" -> ()
        | "sequence" -> ()
        | "record" -> () ] ]
    ;
    quantifiedExpression:
      
      [ [ [ "forall" -> () | "exists"; GREEDY OPT "unique" ]; GREEDY LIST1 variableSetDeclaration SEP ","; "|";
          designRuleExpression ] ]
    ;
    distinctVariableSetDeclaration:
      
      [ [ "distinct"; GREEDY LIST1 identifier SEP ","; GREEDY OPT [ [ ":" | ":!" ]; acmeTypeRef ]; "in";
          [ setExpression | reference ] ] ]
    ;
    variableSetDeclaration:
 
      [ [ distinctVariableSetDeclaration
        | identifier; GREEDY LIST0 [ ","; identifier ]; GREEDY OPT [ [ ":" | ":!" ]; acmeTypeRef ];
          "in"; [ setExpression | reference ] ] ]
    ;
    sequenceExpression:
      
      [ [ "<"; pathExpression; ">" ] ]
    ;
    setExpression:
      
      [ [ literalSet
        | setConstructor
        | pathExpression ] ]
    ;
    pathExpression:
      
      [ [ "/"; reference; GREEDY OPT [ [ ":" | ":!" ]; acmeTypeRef ];
          GREEDY OPT [ "["; designRuleExpression; "]" ];
          GREEDY LIST0 [ "/"; pathExpressionContinuation ] ] ]
    ;
    pathExpressionContinuation:
      
      [ [ setReference; GREEDY OPT [ [ ":" | ":!" ]; acmeTypeRef ];
          GREEDY OPT [ "["; designRuleExpression; "]" ];
          GREEDY LIST0 [ "/"; pathExpressionContinuation ]
        | GREEDY OPT "..."; reference ] ]
    ;
    literalSet:
      
      [ [ "{"; "}" -> ()
        | "{"; [ literalConstant | reference ];
          GREEDY LIST0 [ ","; [ literalConstant | reference ] ]; "}" -> () ] ]
    ;
    literalSequence:
      
      [ [ "<"; ">" -> ()
        | "<"; [ literalConstant | reference ];
          GREEDY LIST0 [ ","; [ literalConstant | reference ] ]; ">" -> () ] ]
    ;
    literalRecordEntry:
      
      [ [ identifier; GREEDY OPT [ ":"; acmePropertyTypeRef ]; "="; literalConstant ] ]
    ;
    literalRecord:
      
      [ [ "["; GREEDY OPT [ GREEDY LIST1 literalRecordEntry SEP ";"; GREEDY OPT ";" ]; "]" ] ]
    ;
    setConstructor:
      
      [ [ GREEDY OPT "{"; "select"; variableSetDeclaration; "|"; designRuleExpression; GREEDY OPT "}"
        | GREEDY OPT "{"; "collect"; reference; ":"; acmeTypeRef; "in";
          [ setExpression | reference ]; "|"; designRuleExpression; GREEDY OPT "}" ] ]
    ;
    acmeTypeRef:
      
      [ [ "system" -> ()
        | "component" -> ()
        | "group" -> ()
        | "connector" -> ()
        | "port" -> ()
        | "role" -> ()
        | "property" -> ()
        | "element" -> ()
        | "type" -> ()
        | "representation" -> ()
        | reference -> ()
        | acmePropertyTypeStructure ] ]
    ;
END;
|foo};
] ;

value parse_acmeCompUnit_eoi = Grammar.Entry.parse Acme.acmeCompUnit_eoi ;

if not Sys.interactive.val then
try
  let (ic, ifname) = match Sys.argv.(1) with [
      x -> (open_in x, x)
    | exception (Invalid_argument _) -> (stdin, "<stdin>")
  ] in do {
    Acmelexer.input_file.val := ifname ;
    let g = parse_acmeCompUnit_eoi (Stream.of_channel ic) in
    print_string "OK\n"
  }
with [ Ploc.Exc loc exc ->
    Fmt.(pf stderr "%s%a@.%!" (Ploc.string_of_location loc) exn exc)
  | exc -> Fmt.(pf stderr "%a@.%!" exn exc)
]
else ()
;
