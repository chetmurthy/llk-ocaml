grammar abbParser;

module
    : moduleData EOF
    ;

moduleData
    : MODULE moduleName NEWLINE
      dataList
      NEWLINE*
      ENDMODULE
    ;

moduleName
    : IDENTIFIER
    | procCall
    ;

dataList
    : (NEWLINE
    | declaration NEWLINE
    | procedure NEWLINE)*
    ;

procedure
    : PROC procCall NEWLINE
      (functionCall NEWLINE)*
    ENDPROC
    ;

procCall
    : procName procParameter?
    ;

procName
    : IDENTIFIER
    ;

procParameter
    : BRACKET_OPEN IDENTIFIER? BRACKET_CLOSE
    ;

functionCall
    : IDENTIFIER (functionParameter COMMA)* functionParameter SEMICOLON
    ;

functionParameter
    : ON_CALL
    | OFF_CALL
    | primitive
    | IDENTIFIER
    ;

declaration
    : init_ type_ IDENTIFIER (EQUALS expression)? SEMICOLON
    ;

type_
    : ( TOOLDATA | WOBJDATA | SPEEDDATA | ZONEDATA | CLOCK | BOOL )
    ;

init_
    : LOCAL? ( CONST | PERS | VAR )
    ;

expression
    : array_ | primitive
    ;

array_
    : SQUARE_OPEN (expression COMMA)* expression SQUARE_CLOSE
    ;

primitive
    : BOOLLITERAL
    | CHARLITERAL
    | STRINGLITERAL
    | (PLUS | MINUS)? FLOATLITERAL
    | (PLUS | MINUS)? INTLITERAL
    ;