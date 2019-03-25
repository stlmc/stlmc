grammar model ;

TRUE  : 'true'  ;
FALSE : 'false' ;
INFTY : 'inf' ;

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

fragment DIGIT      : [0-9] ;

VALUE : MINUS? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)? ;

fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;

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
PROP : 'propositions' ;

BOOL_AND   : 'and' ;
BOOL_OR    : 'or'  ;
BOOL_NOT   : 'not' ;
JUMP_ARROW : '==>' ;
DIFF       : 'd/dt' ;

NOT   : '~'   ;
AND   : '/\\' ;
OR    : '\\/' ;
IMP   : '->'  ;

UNTIL   : 'U'  ;
RELEASE : 'R'  ;
GLOBAL  : '[]' ;
FINAL   : '<>' ;

VARIABLE     : (LOWERCASE | UPPERCASE)+ DIGIT* ;

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

stlMC : (mode_var_decl | variable_var_decl)+ mode_module+ init_decl props goal_decl EOF ;

mode_var_decl     : var_type VARIABLE SEMICOLON ;
variable_var_decl : var_range VARIABLE SEMICOLON ;

expression  : LPAREN expression RPAREN # parenthesisExp
            | expression op=(PLUS | MINUS | MULTIPLY | DIVIDE) expression # binaryExp
            | op=FUNC_OP expression  # unaryExp
            | VALUE     # constantExp
            | VARIABLE  # constantExp
              ;

condition   : LPAREN condition RPAREN  # parenthesisCond
            | condition op=COMPARE_OP condition    # compCond
            | expression op=COMPARE_OP expression  # compExp
            | condition op=(BOOL_AND | BOOL_OR | AND | OR) condition   # binaryCond
            | op=(BOOL_AND | BOOL_OR) condition condition+  # multyCond
            | op=BOOL_NOT condition  # unaryCond
            | TRUE     # constantCond
            | FALSE    # constantCond
            | VALUE    # constantCond
            | VARIABLE # constantCond
              ;

jump_redecl : LPAREN jump_redecl RPAREN   # parenthesisJump
            | jump_redecl op=(BOOL_AND | BOOL_OR | AND | OR) jump_redecl   # binaryJump
            | op=(BOOL_AND | BOOL_OR) jump_redecl jump_redecl+  # multyJump 
            | op=BOOL_NOT jump_redecl  # unaryJump
            | NEXT_VAR # boolVar
            | NEXT_VAR EQUAL TRUE # jumpMod
            | NEXT_VAR EQUAL FALSE # jumpMod
            | NEXT_VAR EQUAL expression # jumpMod
              ;

var_type    : varType=(BOOL | INT | REAL) ;
var_range   : LBRACK VALUE RBRACK #exactValue
            | leftParen=(LBRACK | LPAREN) leftVal=VALUE COMMA rightVal=VALUE rightParen=(RPAREN | RBRACK)  # variableRange
            ;

diff_eq : DIFF LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;
sol_eq : VARIABLE LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;

mode_module : LCURLY mode_decl inv_decl flow_decl jump_decl RCURLY ;

mode_decl : MODE COLON (condition SEMICOLON)+ ;
inv_decl  : INVT COLON (condition SEMICOLON)* ;
flow_decl : FLOW COLON (diff_eq+ | sol_eq+) ;
jump_redecl_module : condition JUMP_ARROW jump_redecl SEMICOLON ;
jump_decl : JUMP COLON (jump_redecl_module)+ ;
 
init_decl : INIT COLON condition SEMICOLON ;

leftEnd
 : LPAREN value=VALUE
 | LBRACK value=VALUE
 ;

rightEnd
 : value=VALUE RPAREN
 | value=VALUE RBRACK
 | value=INFTY  RPAREN
 ;

interval
 : leftEnd COMMA rightEnd
 | EQUAL VALUE
 ;

formula
 :          op=NOT                      formula  # unaryFormula
 |          op=(GLOBAL|FINAL)  interval formula  # unaryTemporalFormula
 | formula  op=(BOOL_AND | BOOL_OR | AND | OR)     formula  # binaryFormula
 | op=(BOOL_AND | BOOL_OR) formula formula+      # multyFormula
 | formula  op=(UNTIL|RELEASE) interval formula  # binaryTemporalFormula
 | formula  op=IMP                      formula  # binaryFormula
 | condition                                     # directCond 
 | LPAREN formula RPAREN                         # parenFormula
 | VARIABLE                                      # proposition
 ;

props : PROP COLON (prop)* ;
prop : VARIABLE EQUAL condition SEMICOLON ;

goal_decl : GOAL COLON (formula SEMICOLON)* ;

 
