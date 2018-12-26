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

INT_NUM : DIGIT+([eE][-+]?DIGIT+)?;
REAL_NUM : DIGIT*'.'?DIGIT+([eE][-+]?DIGIT+)?;

VARIABLE     : (LOWERCASE | UPPERCASE)+ DIGIT* ;
CONSTANT     : TRUE | FALSE | INT_NUM | REAL_NUM ;

BOOL : 'bool' ;
INT  : 'int' ;
REAL : 'real' ;

PLUS     : '+' ;
MINUS    : '-' ;
MULTIPLY : '*' ;
DIVIDE   : '/' ;

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
NEXT_VAR   : VARIABLE + '\'' ;

/*
 * Parser Rules
 */

stlMC : mode_var_decl variable_var_decl (mode_module)+ init_decl goal_decl EOF ;

expression  : LPAREN expression RPAREN # parenthesisExp
            | expression op=(PLUS | MINUS | MULTIPLY | DIVIDE) expression # binaryExp
            | op=FUNC_OP expression  # unaryExp
            | VARIABLE  # constantExp
            | INT_NUM # constantExp
            | REAL_NUM # constantExp
              ;

condition   : LPAREN condition RPAREN  # parenthesisCond
            | expression op=COMPARE_OP expression  # compCond
            | op=(BOOL_AND | BOOL_OR) condition condition  #binaryCond 
            | op=BOOL_NOT condition  # unaryCond
            | TRUE  # constantCond
            | FALSE  # constantCond
            | VARIABLE # constantCond
              ;

jump_redecl_module : NEXT_VAR EQUAL expression ; 
             
jump_redecl : LPAREN jump_redecl RPAREN   # parenthesisJump
            | op=(BOOL_AND | BOOL_OR) jump_redecl jump_redecl  # binaryJump 
            | op=BOOL_NOT jump_redecl jump_redecl  # unaryJump
            | condition  # conditionMod
            | jump_redecl_module # jumpMod
              ;

diff_eq : DIFF LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;
sol_eq : VARIABLE LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;

mode_decl : MODE COLON (condition SEMICOLON)+ ;
inv_decl  : INVT COLON (condition SEMICOLON)* ;
flow_decl : FLOW COLON (diff_eq+ | sol_eq+) ;
jump_decl : JUMP COLON (condition JUMP_ARROW jump_redecl SEMICOLON)+ ; 

mode_var_decl     : (BOOL | INT | REAL) VARIABLE SEMICOLON ;
variable_var_decl : interval VARIABLE SEMICOLON ;

mode_module : LCURLY mode_decl inv_decl flow_decl jump_decl RCURLY ;
 
init_decl : INIT COLON condition SEMICOLON ;
goal_decl : GOAL COLON condition SEMICOLON ;

