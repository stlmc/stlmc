grammar vila;


/*
 * Parser rules
 */


expression
: expression operator=EQ expression
| expression operator=(MUL | DIV) expression
| expression operator=(PLUS | MINUS) expression
| uniop=MINUS value=(NUMBER | VARIABLE)
| value=(NUMBER | VARIABLE)
;


statement
: comment* expression comment* EOF
;

comment
: COMMENT
| COMMENT_2
;




/*
 * Lexer rules
 * Expect there will be no whitespaces at all
 */

fragment DIGIT		: [0-9]							;
EQ			: '='							;
PLUS			: '+' 							;
MINUS			: '-'							;
MUL			: '*'							;
DIV			: '/'							;
WHITEPACE		: (' ' | '\t' | '\n')+ -> skip				;
NUMBER			: DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)?		;
fragment LOWERCASE 	: [a-z] 						;
fragment UPPERCASE 	: [A-Z] 						;
VARIABLE		: (LOWERCASE | UPPERCASE)+ DIGIT*			;
fragment COMMENT_LEFT	: '/*'							;
fragment COMMENT_RIGHT	: '*/'							;
fragment COMMENT_ALONE	: '//'							;
COMMENT			: COMMENT_LEFT .*? COMMENT_RIGHT 			;
COMMENT_2		: COMMENT_ALONE .*? '\n'				;
