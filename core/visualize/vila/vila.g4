grammar vila;


/*
 * Parser rules
 */

statement
: comment* expression comment*
| statement statement EOF
;

expression
: value=(NUMBER | VARIABLE)
| expression operator=(MUL | DIV) expression
| expression operator=(PLUS | MINUS) expression
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
PLUS			: '+' 							;
MINUS			: '-'							;
MUL			: '*'							;
DIV			: '/'							;
WHITEPACE		: (' ' | '\t' | '\n')+ -> skip				;
NUMBER			: MINUS? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)?	;
fragment LOWERCASE 	: [a-z] 						;
fragment UPPERCASE 	: [A-Z] 						;
VARIABLE		: MINUS? (LOWERCASE | UPPERCASE)+ DIGIT*		;
fragment COMMENT_LEFT	: '/*'							;
fragment COMMENT_RIGHT	: '*/'							;
fragment COMMENT_ALONE	: '//'							;
COMMENT			: COMMENT_LEFT .*? COMMENT_RIGHT 			;
COMMENT_2		: COMMENT_ALONE .*? '\n'				;
