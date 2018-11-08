/**
 * Student name: Kim Hoang Long
 * Student ID: 1652758
 */

grammar MP;

@lexer::header {
from lexererr import *
}

options{
	language=Python3;
}


program
	: decl+ EOF
	;

decl
	: vardecl
	| funcdecl
	| procdecl
	;

vardecl
	: VAR vargroup+
	;

vargroup
	: idlist COLON idtype SEMI
	;

idlist
	: ID (COMMA ID)*
	;

idtype
	: primtype
	| arraytype
	;

primtype
	: BOOLEAN
	| INTEGER
	| REAL
	| STRING
	;

arraytype
	: ARRAY LB signedInt DOTDOT signedInt RB OF primtype
	;

signedInt
	: SUB? INTLIT
	;

funcdecl
	: FUNCTION ID LP plist? RP COLON idtype SEMI vardecl? body
	;

plist
	: pgroup (SEMI pgroup)*
	;

pgroup
	: idlist COLON idtype
	;

procdecl
	: PROCEDURE ID LP plist? RP SEMI vardecl? body
	;

body
	: BEGIN stmt* END
	;

stmt
	: assign
	| ifstmt
	| whilestmt
	| forstmt
	| breakstmt
	| continuestmt
	| returnstmt
	| withstmt
	| callstmt
	| cpstmt
	;

cpstmt
	: body
	;

assign
	: (variable ASSIGN)+ expr SEMI
	;

variable
	: ID
	| arraycell
	;

ifstmt
	: IF expr THEN stmt (ELSE stmt)?
	;

whilestmt
	: WHILE expr DO stmt
	;

forstmt
	: FOR ID ASSIGN expr (TO | DOWNTO) expr DO stmt
	;

breakstmt
	: BREAK SEMI
	;

continuestmt
	: CONTINUE SEMI
	;

returnstmt
	: RETURN (expr)? SEMI
	;

withstmt
	: WITH vargroup+ DO stmt
	;

callstmt
	: ID LP (expr (COMMA expr)*)? RP SEMI
	;

expr
	: expr AND THEN exp1
	| expr OR ELSE exp1
	| exp1
	;

exp1
	: exp2 EQUAL exp2
	| exp2 NOTEQUAL exp2
	| exp2 LT exp2
	| exp2 LE exp2
	| exp2 GT exp2
	| exp2 GE exp2
	| exp2
	;

exp2
	: exp2 ADD exp3
	| exp2 SUB exp3
	| exp2 OR exp3
	| exp3
	;

exp3
	: exp3 SLASH exp4
	| exp3 MUL exp4
	| exp3 DIV exp4
	| exp3 MOD exp4
	| exp3 AND exp4
	| exp4
	;

exp4
	: SUB exp4
	| NOT exp4
	| exp5
	;

exp5
	: exp6 LB expr RB
	| exp6
	;

exp6
	: LP expr RP 
	| op
	;

op
	: ID
	| INTLIT
	| FLOATLIT
	| STRINGLIT
	| boollit
	| funcall
	;

funcall
	: ID LP (expr (COMMA expr)*)? RP
	;

arraycell
	: exp6 LB expr RB
	;

boollit
	: TRUE
	| FALSE
	;

fragment LETTER
	: A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
	;

fragment A
	: [aA]
	;

fragment B 
	: [bB]
	;

fragment C 
	: [cC]
	;

fragment D 
	: [dD]
	;

fragment E 
	: [eE]
	;
fragment F 
	: [fF]
	;

fragment G 
	: [gG]
	;

fragment H 
	: [hH]
	;

fragment I 
	: [iI]
	;

fragment J
	: [jJ]
	;

fragment K 
	: [kK]
	;

fragment L
	: [lL]
	;

fragment M 
	: [mM]
	;

fragment N 
	: [nN]
	;

fragment O 
	: [oO]
	;

fragment P 	
	: [pP]
	;

fragment Q 
	: [qQ]
	;

fragment R 
	: [rR]
	;

fragment S 
	: [sS]
	;

fragment T 
	: [tT]
	;

fragment U 
	: [uU]
	;

fragment V 
	: [vV]
	;

fragment W 
	: [wW]
	;

fragment X
	: [xX]
	;

fragment Y
	: [yY]
	;

fragment Z 
	: [zZ]
	;


AND
	: A N D
	;

ARRAY
	: A R R A Y
	;

BEGIN
	: B E G I N
	;

BOOLEAN
	: B O O L E A N
	;

BREAK
	: B R E A K
	;

CONTINUE
	: C O N T I N U E
	;

DIV
	: D I V
	;

DO
	: D O
	;

DOWNTO
	: D O W N T O
	;

ELSE
	: E L S E
	;

END
	: E N D
	;

FALSE
	: F A L S E
	;

FOR
	: F O R
	;

FUNCTION
	: F U N C T I O N
	;

IF
	: I F
	;

INTEGER
	: I N T E G E R
	;

MOD
	: M O D
	;

NOT
	: N O T
	;

OF
	: O F
	;

OR
	: O R
	;

PROCEDURE
	: P R O C E D U R E
	;

REAL
	: R E A L
	;

RETURN
	: R E T U R N
	;

STRING
	: S T R I N G
	;

THEN
	: T H E N
	;

TO
	: T O
	;

TRUE
	: T R U E
	;

VAR
	: V A R
	;

WHILE
	: W H I L E
	;

WITH
	: W I T H
	;


ADD 
	: '+'
	;

SUB     
	: '-'
	;

MUL     
	: '*'
	;

SLASH     
	: '/'
	;


ASSIGN 	
	: ':=' 
	;

COMMA   	
	: ',' 
	;

SEMI    	
	: ';' 
	;

COLON   
	: ':' 
	;

EQUAL  
	: '='
	;

NOTEQUAL 
	: '<>'
	;

LT  
	: '<'
	;

LE  
	: '<='
	;

GT      
	: '>'
	;

GE     
	: '>='
	;


LB      
	: '[' 
	;

RB     	
	: ']' 
	;

LP      
	: '(' 
	;

RP      
	: ')' 
	;

LC      
	: '{' 
	;

RC      
	: '}' 
	;

DOTDOT
	: '..'
	;

WHITESPACE 		
	: [ \t\r\n\f] -> skip
	;

BLOCK_COMMENT	
	: ( '(*' .*? '*)' | '{' .*? '}' ) -> skip
	;

LINE_COMMENT	
	: ( '//' ~[\r\n]* ) -> skip 
	;


ID 
	: (LETTER | '_') (LETTER | '_' | DIGIT)*
	;

INTLIT
	: DIGIT+
	;

FLOATLIT
	: DIGIT+ '.' DIGIT* EXPONENT?
    | '.' DIGIT+ EXPONENT?
    | DIGIT+ EXPONENT
    ;

STRINGLIT
	: '"' STRING_CHARS? '"' { self.text = self.text[1:-1] }
	;

fragment
DIGIT
	: [0-9]
	;

fragment
EXPONENT
	: [eE] [-]? [0-9]+
	;

fragment
ESCAPE_SQ
    : '\\' [btrfn"'\\]
    ;

fragment
STRING_CHAR
    : ~["'\\\b\t\r\f\n]
    | ESCAPE_SQ
    ;

fragment
STRING_CHARS
    : STRING_CHAR+
    ;

UNCLOSE_STRING: '"' STRING_CHAR+
{
raise UncloseString(self.text[1:])
} ;

ILLEGAL_ESCAPE:  '"' STRING_CHAR* ('\\' ~[btfnr"'\\] | [\b\t\f\n\r\\"'])
{
raise IllegalEscape(self.text[1:])
} ;

ERROR_CHAR: .
{
raise ErrorToken(self.text)
} ;