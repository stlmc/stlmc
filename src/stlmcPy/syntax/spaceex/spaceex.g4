grammar spaceex ;

TRUE  : 'true' | 'True' | 'TRUE' ;
FALSE : 'false' | 'False' | 'FALSE' ;
INFTY : 'inf' ;

fragment GT        : '>' ;
fragment GTE       : '>=' ;
fragment LT        : '<' ;
fragment LTE       : '<=' ;

COMPARE_OP : (GT | GTE | LT | LTE) ; 
EQUAL       : '=' ;
NEQ         : '!=' ;

fragment OP_SIN    : 'sin' ;
fragment OP_COS    : 'cos' ;
fragment OP_TAN    : 'tan' ;
fragment OP_ARCSIN : 'arcsin';
fragment OP_ARCCOS : 'arccos';
fragment OP_ARCTAN : 'arctan';
fragment OP_SQRT   : 'sqrt' ;
FUNC_OP : (OP_SIN | OP_COS | OP_TAN | OP_ARCSIN | OP_ARCCOS | OP_ARCTAN | OP_SQRT) ;

PLUS     : '+' ;
MINUS    : '-' ;
MULTIPLY : '*' ;
POWER    : '^' ;
DIVIDE   : '/' ;

MODE : 'mode' ;
INVT : 'inv' ;
FLOW : 'flow' ;
JUMP : 'jump' ;
REACH : 'reach';
GOAL : 'goal' ;
INIT : 'init' ;
PROP : 'proposition' ;
CONST : 'const' ;

COMPONENT : 'component' ;
PARAM : 'param' ;

BOOL : 'bool' | 'Bool' | 'BOOL' ;
INT  : 'int' | 'Int' | 'INT' ;
REAL : 'real' | 'Real' | 'REAL' ;

BOOL_AND   : 'and' | 'And' ;
BOOL_OR    : 'or'  | 'Or' ;
NOT   : 'not' | 'Not' | '~' ;


IMP   : '->'  ;

UNTIL   : 'U'  ;
RELEASE : 'R'  ;
GLOBAL  : '[]' ;
FINAL   : '<>' ;

LCURLY : '{' ;
RCURLY : '}' ;
QUOTE : '"' ;

LPAREN : '(' ;
RPAREN : ')' ;


LBRACK : '[' ;
RBRACK : ']' ;

COMMA  : ',' ;
LABEL : '@';

fragment DIGIT      : [0-9] ;

NINFTY : MINUS INFTY ;  
VALUE : MINUS? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)? ;

fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;

ID: ([a-zA-Z])+([a-zA-Z]+ | '_' | DIGIT+)?;

NEXT_VAR   : ID '\'' ;

WS      : ((' ' | '\t' | '\n' | '\r')+ | COMMENT)-> skip ;

fragment COMMENT : 
                   '#' ~( '\r' | '\n' )* 
		   | '\'\'\'' .*? '\'\'\''
		   ;



/*
 * Parser Rules
 */

sxFlow : flow ;

sxCond : cond ;

sxAssn : assn ;

sxExpr : expr ;

flow  : NEXT_VAR '==' expr # unitFlow
      | flow '&' flow      # andFlow
      | FALSE              # falseFlow
      ;

assn : NEXT_VAR '==' expr  # unitAssn1
      | ID ':=' expr       # unitAssn2
      | assn '&' assn      # andAssn
      ;

expr  : '(' expr ')'        # parExp
      | VALUE               # valExp
      | ID                  # varExp
      | MINUS expr          # unaryMinus
      | FUNC_OP expr        # unaryFunc
      | expr POWER expr     # powExp
      | expr MULTIPLY expr  # mulExp
      | expr DIVIDE expr    # divExp
      | expr PLUS expr      # addExp
      | expr MINUS expr     # subExp
      ;

cond  : '(' cond ')'        # parCond
      | expr '==' expr      # eqCond
      | expr '>' expr       # gtCond
      | expr '>=' expr      # geqCond
      | expr '<' expr       # ltCond
      | expr '<=' expr      # leqCond
      | cond ('&&' | '&') cond  # andCond
      ;
