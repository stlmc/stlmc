grammar model ;

import stl ;

TRUE  : 'true'  ;
FALSE : 'false' ;

fragment GT        : '>' ;
fragment GTE       : '>=' ;
fragment LT        : '<' ;
fragment LTE       : '<=' ; 
fragment COM_EQ    : '==' ;
fragment NEQ       : '!=' ;

COMPARE_OP : (GT | GTE | LT | LTE | COM_EQ | NEQ) ;

fragment OP_SIN    : 'sin' ;
fragment OP_COS    : 'cos' ;
fragment OP_LOG    : 'log' ;
fragment OP_SQRT   : 'sqrt' ;

FUNC_OP : (OP_SIN | OP_COS | OP_LOG | OP_SQRT) ;


fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;

PLUS     : '+' ;
MINUS    : '-' ;
MULTIPLY : '*' ;
DIVIDE   : '/' ;

VALUE : MINUS? NUMBER ;

BOOL : 'bool' ;
INT  : 'int' ;
REAL : 'real' ;

MODE : 'mode' ;
INVT : 'inv' ;
FLOW : 'flow' ;
JUMP : 'jump' ;
GOAL : 'goal' ;
INIT : 'init' ;

BOOL_AND   : 'and' ;
BOOL_OR    : 'or'  ;
BOOL_NOT   : 'not' ;
JUMP_ARROW : '==>' ;
DIFF       : 'd/dt' ;

VARIABLE     : (LOWERCASE | UPPERCASE)+ DIGIT* ;

UNARY_CONST : (MINUS | PLUS)? NUMBER ; 
UNARY_VAR   : (MINUS | PLUS)? VARIABLE ;

LCURLY : '{' ;
RCURLY : '}' ;
COLON : ':' ;
SEMICOLON : ';' ;
LPAREN : '(' ;
RPAREN : ')' ;
LBRACK : '[' ;
RBRACK : ']' ;
COMMA  : ',' ;
EQUAL  : '=' ;

NEXT_VAR   : VARIABLE '\'' ;
WS      : (' ' | '\t' | '\n')+ -> skip ;

/*
 * Parser Rules
 */

stlMC : mode_var_decl+ variable_var_decl+ mode_module+ init_decl goal_decl EOF ;

mode_var_decl     : var_type VARIABLE SEMICOLON ;
variable_var_decl : var_range VARIABLE SEMICOLON ;

expression  : LPAREN expression RPAREN # parenthesisExp
            | expression op=(PLUS | MINUS | MULTIPLY | DIVIDE) expression # binaryExp
            | op=FUNC_OP expression  # unaryExp
            | VALUE     # constantExp
            | VARIABLE  # constantExp
              ;

condition   : LPAREN condition RPAREN  # parenthesisCond
            | condition op=COMPARE_OP condition #compCond
            | expression op=COMPARE_OP expression  # compCond
            | op=(BOOL_AND | BOOL_OR) condition condition+  #multiCond 
            | op=BOOL_NOT condition  # unaryCond
            | TRUE  # constantCond
            | FALSE  # constantCond
            | VARIABLE # constantCond
              ;

jump_redecl : LPAREN jump_redecl RPAREN   # parenthesisJump
            | op=(BOOL_AND | BOOL_OR) jump_redecl jump_redecl+  # multiJump 
            | op=BOOL_NOT jump_redecl  # unaryJump
            | NEXT_VAR # boolVar
            | NEXT_VAR EQUAL expression # jumpMod
              ;

var_type    : (BOOL | INT | REAL) ;
var_range   : LBRACK VALUE RBRACK #exactValue
            | leftParen=(LBRACK | LPAREN) leftVal=VALUE COMMA rightVal=VALUE rightParen=(RPAREN | RBRACK)  # variableRange
            ;

diff_eq : DIFF LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;
sol_eq : VARIABLE LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;

mode_module : LCURLY mode_decl inv_decl flow_decl jump_decl RCURLY ;

mode_decl : MODE COLON (condition SEMICOLON)+ ;
inv_decl  : INVT COLON (condition SEMICOLON)* ;
flow_decl : FLOW COLON (diff_eq+ | sol_eq+) ;
jump_decl : JUMP COLON (condition JUMP_ARROW jump_redecl SEMICOLON)+ ;
 
init_decl : INIT COLON condition SEMICOLON ;

property : VARIABLE EQUAL condition SEMICOLON ;

goal_decl : GOAL COLON stl=(condition | formula)* SEMICOLON ;
 
