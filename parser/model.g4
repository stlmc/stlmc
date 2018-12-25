grammar model ;

import stl ;

fragment GT        : '>' ;
fragment GTE       : '>=' ;
fragment LT        : '<' ;
fragment LTE       : '<=' ; 
fragment EQ        : '==' ;
fragment NEQ       : '!=' ;

COMPARE_OP : (GT | GTE | LT | LTE | EQ | NEQ) ;

fragment OP_SIN    : 'sin' ;
fragment OP_COS    : 'cos' ;
fragment OP_LOG    : 'log' ;
fragment OP_SQRT   : 'sqrt' ;

FUNC_OP : (OP_SIN | OP_COS | OP_LOG | OP_SQRT) ;


fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;

VARIABLE     : (LOWERCASE | UPPERCASE)+ DIGIT* ;
CONSTANT     : TRUE | FALSE | NUMBER ;

PLUS     : '+' ;
MINUS    : '-' ;
MULTIPLY : '*' ;
DIVIDE   : '/' ;

BOOL : 'bool' ;
INT  : 'int' ;
REAL : 'real' ;

MODE : 'mode' ;
INVT : 'inv' ;
FLOW : 'flow' ;
JUMP : 'jump' ;
GOAL : 'goal' ;
INIT : 'init' ;

LCURLY : '{' ;
RCURLY : '}' ;
COLON : ':' ;
SEMICOLON : ';' ;

BOOL_AND   : 'and' ;
BOOL_OR    : 'or'  ;
BOOL_NOT   : 'not' ;   
JUMP_ARROW : '==>' ;
DIFF       : 'd/dt' ;

/*
 * Parser Rules
 */

stlMC : mode_var_decl variable_var_decl (mode_module)+ init_decl goal_decl EOF ;

expression : expression PLUS expression |
             expression MINUS expression |
             expression MULTIPLY expression |
             expression DIVIDE expression |
             FUNC_OP expression |
             VARIABLE |
             NUMBER ;

condition : LPAREN condition RPAREN |
             expression COMPARE_OP expression |
             BOOL_AND condition condition |
             BOOL_OR condition condition |
             BOOL_NOT condition |
             TRUE |
             FALSE |
             VARIABLE ;
             
diff_eq : DIFF LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;
sol_eq : VARIABLE LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;

mode_decl : MODE COLON (condition SEMICOLON)+ ;
inv_decl  : INVT COLON (condition SEMICOLON)* ;
flow_decl : FLOW COLON (diff_eq+ | sol_eq+) ;
jump_decl : JUMP COLON (condition JUMP_ARROW condition SEMICOLON)+ ; 

mode_var_decl     : (BOOL | INT | REAL) VARIABLE SEMICOLON ;
variable_var_decl : interval VARIABLE SEMICOLON ;

mode_module : LCURLY mode_decl inv_decl flow_decl jump_decl RCURLY ;
 
init_decl : INIT COLON condition SEMICOLON ;
goal_decl : GOAL COLON condition SEMICOLON ;

