grammar CMinus;

program
    :   declaration+
    ;

declaration
    :   variable
    |   function
    ;

// ack is $function.st ambig?  It can mean the rule's dyn scope or
// the ref in this rule.  Ack.

variable
    :   type declarator ';'
    ;

declarator
    :   ID
    ;

function
    :   type ID
        '(' ( formalParameter ( ',' formalParameter )* )? ')'
        block
    ;

formalParameter
    :   type declarator 
    ;

type
    :   'int'
    |   'char'
    |   ID
    ;

block
    :  '{'
       ( variable )*
       ( stat )*
       '}'
    ;

stat
    : forStat
    | expr ';'
    | block
    | assignStat ';'
    | ';'
    ;

forStat
    :   'for' '(' assignStat ';' expr ';' assignStat ')' block
    ;

assignStat
    :   ID '=' expr
    ;

expr:   condExpr
    ;

condExpr
    :   aexpr
        (   (  '==' expr
            |  '<' aexpr
            )
        |
        )
    ;

aexpr
    :   (atom)
        ( '+' atom )*
    ;

atom
    : ID
    | INT
    | '(' expr ')'
    ; 

/*

ID  :   ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*
    ;

INT	:	('0'..'9')+
	;

WS  :   (' ' | '\t' | '\r' | '\n')+ {$channel=HIDDEN;}
    ;    
*/
