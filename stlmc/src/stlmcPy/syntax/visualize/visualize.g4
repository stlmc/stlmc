grammar visualize ;

LCURLY : '{' ;
RCURLY : '}' ;
LPAREN : '(' ;
RPAREN : ')' ;
COMMA  : ',' ;
OUTPUT : 'output' ;
GROUP : 'group' ;
EQ : '=' ;

fragment DIGIT      : [0-9] ;
fragment LOWERCASE : [a-z] ;
fragment UPPERCASE : [A-Z] ;

VARIABLE     : (ID)+ (LOWERCASE | UPPERCASE | DIGIT)* ;
ID: ([a-zA-Z] | '_' | '-' | DIGIT )+;

WS      : ((' ' | '\t' | '\n' | '\r')+ | COMMENT)-> skip ;

fragment COMMENT : 
                   '#' ~( '\r' | '\n' )* 
		   | '\'\'\'' .*? '\'\'\''
		   ;

/*
 * Parser Rules
 */

vis_config: LCURLY body RCURLY EOF ;
body: output? group?
    | group? output? ;

output: OUTPUT EQ VARIABLE ;
group: GROUP LCURLY group_list RCURLY;
group_list: # empty_group
    | LPAREN variable_list RPAREN # base_group
    | group_list COMMA group_list # other_group_list ;
variable_list: # empty_var_list
    | VARIABLE # base_var_list
    | variable_list COMMA variable_list # other_var_list ;