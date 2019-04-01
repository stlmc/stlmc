grammar model ;

TRUE  : 'true' | 'True' | 'TRUE' ;
FALSE : 'false' | 'False' | 'FALSE' ;
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
PROP : 'propositions' ;

BOOL : 'bool' | 'Bool' | 'BOOL' ;
INT  : 'int' | 'Int' | 'INT' ;
REAL : 'real' | 'Real' | 'REAL' ;

BOOL_AND   : 'and' | 'And' ;
BOOL_OR    : 'or'  | 'Or' ;
NOT   : 'not' | 'Not' | '~' ;
JUMP_ARROW : '==>' ;
DIFF       : 'd/dt' ;

AND   : '/\\' ;
OR    : '\\/' ;
IMP   : '->'  ;

UNTIL   : 'U'  ;
RELEASE : 'R'  ;
GLOBAL  : '[]' ;
FINAL   : '<>' ;

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

fragment DIGIT      : [0-9] ;

VALUE : MINUS? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)? ;

fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;

VARIABLE     : (LOWERCASE | UPPERCASE)+ DIGIT* ;

NEXT_VAR   : VARIABLE '\'' ;

WS      : (' ' | '\t' | '\n')+ -> skip ;


/*
 * Parser Rules
 */

stlMC : (mode_var_decl | variable_var_decl)+ mode_module+ init_decl (props)? goal_decl EOF ;

mode_var_decl     : var_type VARIABLE SEMICOLON ;
variable_var_decl : var_range VARIABLE SEMICOLON ;

expression  : 
              LPAREN expression RPAREN # parenthesisExp
            | VALUE     # constantExp
            | VARIABLE  # constantExp
            | expression op=(PLUS | MINUS | MULTIPLY | DIVIDE) expression # binaryExp
            | op=FUNC_OP expression  # unaryExp
              ;

condition   :
              LPAREN condition RPAREN  # parenthesisCond
            | TRUE     # constantCond
            | FALSE    # constantCond
            | VALUE    # constantCond
            | VARIABLE # constantCond
            | expression op=COMPARE_OP expression  # compExp
            | condition op=COMPARE_OP condition    # compCond
            | condition op=(BOOL_AND | BOOL_OR | AND | OR) condition   # binaryCond
            | op=(BOOL_AND | BOOL_OR) condition condition+  # multyCond
            | op=NOT condition  # unaryCond
              ;

jump_redecl : LPAREN jump_redecl RPAREN   # parenthesisJump
            | jump_redecl op=(BOOL_AND | BOOL_OR | AND | OR) jump_redecl   # binaryJump
            | op=(BOOL_AND | BOOL_OR) jump_redecl jump_redecl+  # multyJump 
            | op=NOT jump_redecl  # unaryJump
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
 :
   LPAREN formula RPAREN                         # parenFormula
 | VARIABLE                                      # proposition
 | formula  op=(BOOL_AND | BOOL_OR | AND | OR)     formula  # binaryFormula
 |          op=NOT                      formula  # unaryFormula
 |          op=(GLOBAL|FINAL)  interval formula  # unaryTemporalFormula
 | op=(BOOL_AND | BOOL_OR) formula formula+      # multyFormula
 | formula  op=(UNTIL|RELEASE) interval formula  # binaryTemporalFormula
 | formula  op=IMP                      formula  # binaryFormula
 ;

props : PROP COLON (prop)* ;
prop : VARIABLE EQUAL condition SEMICOLON ;

goal_decl : GOAL COLON (formula SEMICOLON)* ;

 
