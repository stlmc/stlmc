grammar flow ;

DELIM           : '\t\r' ;
LINE            : '\n' ;
WS              : DELIM+ ;
fragment DIGIT  : [0-9] ;
fragment LETTER : [a-zA-z] ;

IDENT           : LETTER (LETTER | DIGIT | '.')* ;
NUMBER          : ('-'?)((DIGIT+)|(DIGIT*'.'DIGIT*)|(DIGIT+'e'((DIGIT+)|('-'DIGIT+)))|(DIGIT*'.'DIGIT*'e'((DIGIT+)|('-'DIGIT+)))|(DIGIT*'.'DIGIT*'e'('+'(DIGIT+)|('-'DIGIT+)))) ;

BACKSLASH       : '\'' ;
PLUS            : '+' ;
MULTIPLY        : '*' ;
MINUS           : '-' ;
EQUAL           : '=' ;
GEQ             : '>=' ;
LEQ             : '<=' ;
COMMA           : ',' ;
SEMICOLON       : ';' ;
COLON           : ':' ;
LBRACK          : '(' ;
RBRACK          : ')' ;
LCURLY          : '{' ;
RCURLY          : '}' ;
LBBRACK         : '[' ;
RBBRACK         : ']' ;
ASSIGN          : ':=' ;
POWER           : '^' ;
SLASH           : '/' ;
RIGHTARROW      : '>' ;

MODE            : 'mode' ;
INIT            : 'init' ;
IN              : 'in' ;
POLYODE1        : 'poly ode 1' ;
POLYODE2        : 'poly ode 2' ;
POLYODE3        : 'poly ode 3' ;
VISUALIZE       : 'visualize' ;
END             : 'end' ;
SETTING         : 'setting' ;
CONTREACH       : 'continuous reachability' ;
HYBRIDREACH     : 'hybrid reachability' ;
FIXEDSTEPS      : 'fixed steps' ;
ADAPTIVEST      : 'adaptive steps' ;
FIXEDORD        : 'fixed orders' ;
ADAPTIVEORD     : 'adaptive orders' ;
ORDER           : 'order' ;
MIN             : 'min' ;
MAX             : 'max' ;
REMEST          : 'remainder estimation' ;
INTERVAL        : 'interval' ;
OCTAGON         : 'octagon' ;
GRID            : 'grid' ;
PLOT            : 'plot' ;
TM              : 'tm' ;
QRPRECOND       : 'QR precondition' ;
IDPRECOND       : 'identity precondition' ;
TIME            : 'time' ;
MODES           : 'modes' ;
JUMPS           : 'jumps' ;
INV             : 'inv' ;
GUARD           : 'guard' ;
RESET           : 'reset' ;
START           : 'start' ;
MAXJMPS         : 'max jumps' ;
OUTPUT          : 'output' ;
NOOUTPUT        : 'no output' ;
PRINTON         : 'print on ';
PRINTOFF        : 'print off' ;
UNSAFESET       : 'unsafe' ;
STATEVAR        : 'state var' ;
TMVAR           : 'tm var' ;
PARAAGGREG      : 'parallelotope aggregation' ;
INTAGGREG       : 'interval aggregation' ;
TMAGGREG        : 'taylor model aggregation' ;
CONTINUOUSFLOW  : 'continuous flowpipes' ;
LINEARCONTINUOUSFLOW    : 'linear continuous flowpipes' ;
HYBRIDFLOW      : 'hybrid flowpipes' ;
TAYLOR_PICARD   : 'taylor picard' ;
TAYLOR_REMAINDER : 'taylor remainder' ;
TAYLOR_POLYNOMIAL : 'taylor polynomial' ;
NONPOLY_CENTER:'nonpolynomial center';
EXP:'exp' ;
SIN:'sin' ;
COS:'cos' ;
LOG:'log' ;
SQRT:'sqrt' ;
NPODE_TAYLOR:'nonpoly ode' ;
CUTOFF:'cutoff' ;
PRECISION:'precision' ;
GNUPLOT:'gnuplot' ;
MATLAB:'matlab' ;
COMPUTATIONPATHS:'computation paths' ;
PAR:'par' ;
UNC:'uncertain' ;
LTI_ODE:'lti ode' ;
LTV_ODE:'ltv ode' ;
UNIVARIATE_POLY:'univariate polynomial' ;
TIME_INV:'time-inv' ;
TIME_VAR:'time-var' ;
STEP:'step' ;
TRUE:'true' ;
FALSE:'false' ;



fragment COMMENT : '#' ;

/*
 * Parser Rules
 */

flowstar :
stateVarDecls modeDecls COMPUTATIONPATHS '{' computation_paths '}' plotting output_env unsafe_hybrid HYBRIDFLOW '{' hybrid_flowpipes '}' ;

stateVarDecls: STATEVAR stateIdDeclList ;
stateIdDeclList: stateIdDeclList ',' IDENT | IDENT ;

modeDecls:
    modeDecls IDENT '{' '{' ORDER NUM '}' '{' CUTOFF NUM '}' '{' polynomial_constraints '}' '}'
    | IDENT '{' '{' ORDER NUM '}' '{' CUTOFF NUM '}' '{' polynomial_constraints '}' '}' ;


polynomial_constraints:
    polynomial_constraints constraint_polynomial LEQ NUM
    | polynomial_constraints constraint_polynomial GEQ NUM
    | polynomial_constraints constraint_polynomial EQ NUM
    | polynomial_constraints constraint_polynomial BELONGSTO '[' NUM ',' NUM ']'
    | polynomial_constraints constraint_polynomial LEQ IDENT
    | polynomial_constraints constraint_polynomial GEQ IDENT
    | polynomial_constraints constraint_polynomial EQ IDENT
    | polynomial_constraints constraint_polynomial BELONGSTO '[' IDENT ',' IDENT ']'
    |
    ;

constraint_polynomial:
    constraint_polynomial '+' constraint_polynomial
    | constraint_polynomial '-' constraint_polynomial
    | '(' constraint_polynomial ')'
    | constraint_polynomial '*' constraint_polynomial
    | constraint_polynomial '^' NUM
    | '-' constraint_polynomial
    | IDENT
    | NUM
    ;

computation_paths:
    computation_paths computation_path ';'
    | computation_path ';'
    ;

computation_path:
    computation_path '(' NUM ',' '[' NUM ',' NUM ']' ')' '-' '>' IDENT
    | IDENT
    ;



plotting:
    GNUPLOT INTERVAL IDENT ',' IDENT
    | GNUPLOT OCTAGON IDENT ',' IDENT
    | GNUPLOT GRID NUM IDENT ',' IDENT
    | MATLAB INTERVAL IDENT ',' IDENT
    | MATLAB OCTAGON IDENT ',' IDENT
    | MATLAB GRID NUM IDENT ',' IDENT
    ;


output_env:
    OUTPUT IDENT
    | PLOT OUTPUT IDENT
    | TM OUTPUT IDENT
    | NOOUTPUT
    ;

unsafe_hybrid: UNSAFESET '{' hybrid_constraints '}';

hybrid_constraints:
    hybrid_constraints IDENT '{' polynomial_constraints '}'
    |
    ;

hybrid_flowpipes



//
//
//stlMC : (mode_var_decl | variable_var_decl | var_val_decl)+ mode_module+ init_decl (props)? goal_decl EOF ;
//
//var_val_decl      : CONST var_type VARIABLE EQUAL val=(VALUE | TRUE| FALSE) SEMICOLON;
//mode_var_decl     : var_type VARIABLE SEMICOLON ;
//variable_var_decl : var_range VARIABLE SEMICOLON ;
//
//expression  :
//              LPAREN expression RPAREN # parenthesisExp
//            | VALUE     # constantExp
//            | TIME      # constantExp
//            | VARIABLE  # constantExp
//            | INITIALVAL # initialValue
//            | op=(MINUS | FUNC_OP) expression    # unaryExp
//	    | expression op=POWER expression #binaryExp
//	    | expression op=(MULTIPLY | DIVIDE ) expression #binaryExp
//            | expression op=(PLUS | MINUS) expression # binaryExp
//            ;
//
//condition   :
//              LPAREN condition RPAREN  # parenthesisCond
//            | TRUE     # constantCond
//            | FALSE    # constantCond
//            | VALUE    # constantCond
//            | VARIABLE # constantCond
//            | op=NOT condition  # unaryCond
//            | condition op=(EQUAL | NEQ) condition    # compCond
//            | expression op=(COMPARE_OP | EQUAL | NEQ) expression  # compExp
//            | op=(BOOL_AND | BOOL_OR) condition condition+  # multyCond
//              ;
//
//jump_redecl : LPAREN jump_redecl RPAREN   # parenthesisJump
//            | op=(BOOL_AND | BOOL_OR) jump_redecl jump_redecl+  # multyJump
//            | op=NOT jump_redecl  # unaryJump
//            | NEXT_VAR # boolVar
//            | NEXT_VAR op=EQUAL TRUE # jumpMod
//            | NEXT_VAR op=EQUAL FALSE # jumpMod
//            | NEXT_VAR op=(COMPARE_OP | EQUAL | NEQ) expression # jumpMod
//              ;
//
//var_type    : varType=(BOOL | INT | REAL) ;
//var_range   : LBRACK VALUE RBRACK #exactValue
//            | leftParen=(LBRACK | LPAREN) leftVal=(NINFTY | VALUE) COMMA rightVal=(VALUE | INFTY) rightParen=(RPAREN | RBRACK)  # variableRange
//            ;
//
//diff_eq : DIFF LBRACK VARIABLE RBRACK EQUAL expression SEMICOLON ;
//sol_eq : VARIABLE LPAREN TIME RPAREN EQUAL expression SEMICOLON ;
//
//mode_module : LCURLY mode_decl inv_decl flow_decl jump_decl RCURLY ;
//
//mode_decl : MODE COLON (condition SEMICOLON)+ ;
//inv_decl  : INVT COLON (condition SEMICOLON)* ;
//flow_decl : FLOW COLON (diff_eq+ | sol_eq+) ;
//jump_redecl_module : condition JUMP_ARROW jump_redecl SEMICOLON ;
//jump_decl : JUMP COLON (jump_redecl_module)* ;
//
//init_decl : INIT COLON condition SEMICOLON ;
//
//leftEnd
// : LPAREN value=VALUE
// | LBRACK value=VALUE
// ;
//
//rightEnd
// : value=VALUE RPAREN
// | value=VALUE RBRACK
// | value=INFTY  RPAREN
// ;
//
//interval
// : leftEnd COMMA rightEnd
// | EQUAL VALUE
// ;
//
//formula
// :
//   LPAREN formula RPAREN                                # parenFormula
// |          op=NOT                      formula         # unaryFormula
// | formula  op=(BOOL_AND | BOOL_OR)     formula         # binaryFormula
// |          op=(GLOBAL|FINAL)  interval formula         # unaryTemporalFormula
// | op=(BOOL_AND | BOOL_OR) formula formula+             # multyFormula
// | formula  op=(UNTIL|RELEASE) interval formula         # binaryTemporalFormula
// | formula  op=IMP                      formula         # binaryFormula
// | TRUE                                                 # constFormula
// | FALSE                                                # constFormula
// | VARIABLE                                             # proposition
// | expression op=(COMPARE_OP | EQUAL | NEQ) expression  # directCond
// ;
//
//props : PROP COLON (prop)* ;
//prop : VARIABLE EQUAL condition SEMICOLON ;
//
//goal_unit : formula # stlGoal
//            | REACH condition # reachGoal
//            ;
//goal_decl : GOAL COLON (goal_unit SEMICOLON)* ;
//
//
