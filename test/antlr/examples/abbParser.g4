grammar abbParser;

module_
    : moduleData EOI
    ;

moduleData
    : MODULE moduleName NEWLINE
      dataList
      NEWLINE*
      ENDMODULE
    ;

moduleName
    : procCall
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

MODULE = 'module' ;
ENDMODULE = 'endmodule' ;
PROC = 'proc' ;
ENDPROC = 'endproc';
LOCAL = 'local' ;
CONST = 'const' ;
PERS = 'pers';
VAR = 'var' ;
TOOLDATA = 'tooldata' ;
WOBJDATA = 'wobjdata' ;
SPEEDDATA = 'speeddata' ;
ZONEDATA = 'zonedata' ;
CLOCK = 'clock' ;
BOOL = 'bool' ;
SLASH               = '/' ;
EQUALS              = ':=' ;
COMMA               = ',';
CURLY_OPEN          = '{';
CURLY_CLOSE         = '}';
COLON               = ':';
SEMICOLON           = ';';
BRACKET_OPEN        = '(';
BRACKET_CLOSE       = ')';
SQUARE_OPEN         = '[';
SQUARE_CLOSE        = ']';
DOT                 = '.';
DOUBLEDOT           = '..';
REL_BIGGER          = '>';
REL_BIGGER_OR_EQUAL = '>=';
REL_SMALLER         = '<';
REL_SMALLER_OR_EQUAL= '<=';
REL_EQUAL           = '==';
REL_NOTEQUAL        = '<>';
PLUS                = '+';
MINUS               = '-';
MULTIPLY            = '*';
PERCENT             = '%';
HASH                = '#';
