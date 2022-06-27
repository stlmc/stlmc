grammar config ;

RUNALL: 'run-all';
RUNLABELED: 'run-labeled-only';
MANDATORY: 'mandatory';
EXTENDS: 'extends';

//conf_dict["fixed steps"] = "0.01"
//    # conf_dict["initially"] = "\"{}\"".format(infix(And(init_children)))
//    conf_dict["time"] = "1"
//    conf_dict["remainder estimation"] = "1e-2"
//    conf_dict["identity precondition"] = ""
//    conf_dict["gnuplot octagon"] = ""
//    conf_dict["adaptive orders"] = "{ min 4 , max 8 }"
//    conf_dict["cutoff"] = "1e-12"
//    conf_dict["precision"] = "53"
//    conf_dict["no output"] = ""
//    conf_dict["max jumps"] = "10"


LCURLY : '{' ;
RCURLY : '}' ;
LTUPLE : '(';
RTUPLE : ')';
COMMA  : ',' ;
QUOTE : '"' ;
EQ : '=' ;

fragment DIGIT      : [0-9] ;
NUMBER : '-'? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)? ;
VALUE: ([a-zA-Z] | '_' | '-' | DIGIT | '/' | '.')+;

WS      : ((' ' | '\t' | '\n' | '\r')+ | COMMENT)-> skip ;

fragment COMMENT : 
                   '#' ~( '\r' | '\n' )* 
		   | '\'\'\'' .*? '\'\'\''
		   ;

/*
 * Parser Rules
 */

config : section* EOF ;

section: VALUE LCURLY args RCURLY # basic_section
       | VALUE EXTENDS names LCURLY args RCURLY # extend_section
        ;

names: VALUE COMMA names # list_of_name
    |  VALUE # single_names
    ;


args: (arg_assn)*;
arg_assn: arg EQ value;

arg : VALUE;
value: QUOTE VALUE QUOTE # string_val
    | QUOTE varible_names QUOTE # multi_string_val
    | RUNALL # runall_val
    | RUNLABELED # runlabeled_only
    | NUMBER # number_val
    | # empty_val
    ;

varible_names: VALUE COMMA varible_names # list_of_variable_names
            |  VALUE # single_variable_name
            ;