grammar stl;

NOT : '~'   ;
AND : '/\\' ;
OR  : '\\/' ;
IMP : '->'  ;
 
TRUE  : 'true'  ;
FALSE : 'false' ;
INFTY : 'inf'   ;

UNTIL   : 'U'  ;
RELEASE : 'R'  ;
GLOBAL  : '[]' ;
FINAL   : '<>' ;
  
LPAREN : '(' ;
RPAREN : ')' ;
LBRACK : '[' ;
RBRACK : ']' ;
COMMA  : ',' ;
EQUAL  : '=' ;
  
ID      : [a-z]+DIGIT* ;
NUMBER  : DIGIT*'.'?DIGIT+([eE][-+]?DIGIT+)? ; 
WS      : [ \r\t\u000C\n]+ -> skip ; 

fragment DIGIT      : [0-9] ;

leftEnd
 : LPAREN value=NUMBER
 | LBRACK value=NUMBER
 ;

rightEnd
 : value=NUMBER RPAREN
 | value=NUMBER RBRACK
 | value=INFTY  RPAREN
 ;

interval
 : leftEnd COMMA rightEnd
 | EQUAL NUMBER
 ;

formula
 :          op=NOT                      formula  # unaryFormula
 |          op=(GLOBAL|FINAL)  interval formula  # unaryTemporalFormula
 | formula  op=AND                      formula  # binaryFormula
 | formula  op=OR                       formula  # binaryFormula
 | formula  op=(UNTIL|RELEASE) interval formula  # binaryTemporalFormula
 | formula  op=IMP                      formula  # binaryFormula
 | LPAREN formula RPAREN                         # parenFormula
 | ID                                            # proposition
 | TRUE                                          # constant
 | FALSE                                         # constant
 ;

