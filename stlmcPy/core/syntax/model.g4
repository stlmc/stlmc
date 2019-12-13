grammar model ;

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
fragment OP_LOG    : 'log' ;
fragment OP_SQRT   : 'sqrt' ;
FUNC_OP : (OP_SIN | OP_COS | OP_TAN | OP_LOG | OP_SQRT) ;

PLUS     : '+' ;
MINUS    : '-' ;
MULTIPLY : '*' ;
POWER    : '**' ;
DIVIDE   : '/' ;

MODE : 'mode' ;
INVT : 'inv' ;
FLOW : 'flow' ;
JUMP : 'jump' ;
GOAL : 'goal' ;
INIT : 'init' ;
PROP : 'propositions' ;
CONST : 'const' ;

BOOL : 'bool' | 'Bool' | 'BOOL' ;
INT  : 'int' | 'Int' | 'INT' ;
REAL : 'real' | 'Real' | 'REAL' ;

BOOL_AND   : 'and' | 'And' ;
BOOL_OR    : 'or'  | 'Or' ;
NOT   : 'not' | 'Not' | '~' ;
JUMP_ARROW : '=>' ;
DIFF       : 'd/dt' ;

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

fragment DIGIT      : [0-9] ;

NINFTY : MINUS INFTY ;  
VALUE : MINUS? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)? ;

fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;
TIME : 't' ;

VARIABLE     : (LOWERCASE | UPPERCASE)+ (LOWERCASE | UPPERCASE | DIGIT)* ;

INITIALVAL : VARIABLE '(0)' ;

NEXT_VAR   : VARIABLE '\'' ;

WS      : ((' ' | '\t' | '\n' | '\r')+ | COMMENT)-> skip ;

fragment COMMENT : 
                   '#' ~( '\r' | '\n' )* 
		   | '\'\'\'' .*? '\'\'\''
		   ;

/*
 * Parser Rules
 */

stlMC : (mode_var_decl | variable_var_decl | var_val_decl)+ mode_module+ init_decl (props)? goal_decl EOF ;

var_val_decl      : CONST var_type VARIABLE EQUAL val=(VALUE | TRUE| FALSE) SEMICOLON;
mode_var_decl     : var_type VARIABLE SEMICOLON ;
variable_var_decl : var_range VARIABLE SEMICOLON ;

expression  : 
              LPAREN expression RPAREN # parenthesisExp
            | VALUE     # constantExp
            | TIME      # constantExp
            | VARIABLE  # constantExp
            | INITIALVAL # initialValue
            | op=(MINUS | FUNC_OP) expression    # unaryExp
	    | expression op=POWER expression #binaryExp
	    | expression op=(MULTIPLY | DIVIDE ) expression #binaryExp
            | expression op=(PLUS | MINUS) expression # binaryExp
            ;

condition   :
              LPAREN condition RPAREN  # parenthesisCond
            | TRUE     # constantCond
            | FALSE    # constantCond
            | VALUE    # constantCond
            | VARIABLE # constantCond
            | op=NOT condition  # unaryCond
            | expression op=(COMPARE_OP | EQUAL | NEQ) expression  # compExp
            | condition op=(COMPARE_OP | EQUAL |NEQ) condition    # compCond
            | condition op=(BOOL_AND | BOOL_OR) condition   # binaryCond
            | op=(BOOL_AND | BOOL_OR) condition condition+  # multyCond
              ;

jump_redecl : LPAREN jump_redecl RPAREN   # parenthesisJump
            | jump_redecl op=(BOOL_AND | BOOL_OR) jump_redecl   # binaryJump
            | op=(BOOL_AND | BOOL_OR) jump_redecl jump_redecl+  # multyJump 
            | op=NOT jump_redecl  # unaryJump
            | NEXT_VAR # boolVar
            | NEXT_VAR op=EQUAL TRUE # jumpMod
            | NEXT_VAR op=EQUAL FALSE # jumpMod
            | NEXT_VAR op=(COMPARE_OP | EQUAL | NEQ) expression # jumpMod
              ;

var_type    : varType=(BOOL | INT | REAL) ;
var_range   : LBRACK VALUE RBRACK #exactValue
            | leftParen=(LBRACK | LPAREN) leftVal=(NINFTY | VALUE) COMMA rightVal=(VALUE | INFTY) rightParen=(RPAREN | RBRACK)  # variableRange
            ;

diff_eq : DIFF LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;
sol_eq : VARIABLE LPAREN TIME RPAREN EQUAL expression SEMICOLON ;

mode_module : LCURLY mode_decl inv_decl flow_decl jump_decl RCURLY ;

mode_decl : MODE COLON (condition SEMICOLON)+ ;
inv_decl  : INVT COLON (condition SEMICOLON)* ;
flow_decl : FLOW COLON (diff_eq+ | sol_eq+) ;
jump_redecl_module : condition JUMP_ARROW jump_redecl SEMICOLON ;
jump_decl : JUMP COLON (jump_redecl_module)* ;
 
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
 | formula  op=(BOOL_AND | BOOL_OR)     formula  # binaryFormula
 |          op=NOT                      formula  # unaryFormula
 |          op=(GLOBAL|FINAL)  interval formula  # unaryTemporalFormula
 | op=(BOOL_AND | BOOL_OR) formula formula+      # multyFormula
 | formula  op=(UNTIL|RELEASE) interval formula  # binaryTemporalFormula
 | formula  op=IMP                      formula  # binaryFormula
 | TRUE                                          # constFormula
 | FALSE                                         # constFormula
 | VARIABLE                                      # proposition
 | condition                                     # directCond
 ;

props : PROP COLON (prop)* ;
prop : VARIABLE EQUAL condition SEMICOLON ;

goal_decl : GOAL COLON (formula SEMICOLON)* ;

 
