grammar config ;

BOUND : 'bound' ;
FORMULA : 'formula' ;
TIME_BOUND: 'time-bound' ;
FORMULA_ENCODING: 'formula-encoding' ;
PRINT_OUTPUT: 'print-output';
DELTA: 'delta';
LOGIC: 'logic';

// solvers
Z3: 'z3';
YICES: 'yices';
SSMT: 'ssmt';
//DREAL: 'dreal';
FLOWSTAR: 'flowstar';
FLOWSTAR_MERGING: 'flowstar-merging';
SPACEEX: 'spaceex';
C2E2: 'c2e2';
//HYLAA: 'hylaa';

TIME: 'time';
KVALUE: 'kvalue';
MAX_DIS_COMP: 'max discrete computation';
ABS_ERR: 'relative error';
REL_ERR: 'absolute error';


// flowstar specific configuration
FS_FIXED_STEPS: 'fixed steps';
FS_INITIALLY: 'initially';
FS_REMAINDER_ESTI: 'remainder estimation';
FS_ID_PRECOND: 'identity precondition';
FS_GNUPLOT_OCTAGON: 'gnuplot octagon';
FS_ADAPTIVE_ORDER: 'adaptive orders';
FS_CUT_OFF: 'cutoff';
FS_PRECISION: 'precision';
FS_NO_OUTPUT: 'no output';
FS_MAX_JUMPS: 'max jumps';


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
COMMA  : ',' ;
QUOTE : '"' ;
EQ : '=' ;

fragment DIGIT      : [0-9] ;
NUMBER : '-'? DIGIT+ ('.' DIGIT+)? ;
NUMBER1 : '-'? DIGIT+ ('.' DIGIT+)? ([eE][-+]?DIGIT+)? ;
VALUE: ([a-zA-Z] | '_' | '-' | DIGIT )+;

WS      : ((' ' | '\t' | '\n' | '\r')+ | COMMENT)-> skip ;

fragment COMMENT : 
                   '#' ~( '\r' | '\n' )* 
		   | '\'\'\'' .*? '\'\'\''
		   ;

/*
 * Parser Rules
 */

config : base_config+ solver_config+ EOF ;
base_config: bound_config | formula_config | formula_encoding_config | time_bound_config | print_config | delta_config ;

bound_config: BOUND EQ QUOTE NUMBER COMMA NUMBER COMMA NUMBER QUOTE                                     # bd_conf_3
           | BOUND EQ QUOTE NUMBER COMMA NUMBER QUOTE                                                   # bd_conf_2
           | BOUND EQ QUOTE NUMBER QUOTE                                                                # bd_conf_1
           ;

formula_config: FORMULA EQ QUOTE NUMBER COMMA NUMBER COMMA NUMBER QUOTE                                 # f_conf_3
           | FORMULA EQ QUOTE NUMBER COMMA NUMBER QUOTE                                                 # f_conf_2
           | FORMULA EQ QUOTE NUMBER QUOTE                                                              # f_conf_1
           ;

formula_encoding_config: FORMULA_ENCODING EQ QUOTE VALUE QUOTE ;

time_bound_config: TIME_BOUND EQ NUMBER;
print_config: PRINT_OUTPUT EQ QUOTE VALUE QUOTE ;
delta_config: DELTA EQ NUMBER ;

solver_config: FLOWSTAR LCURLY flowstar_configs? RCURLY                                                      # flowstar_conf
             | FLOWSTAR_MERGING LCURLY flowstar_configs? RCURLY                                              # flowstar_merging_conf
             | YICES LCURLY yices_configs? RCURLY                                                      # yices_conf
             | Z3 LCURLY z3_configs? RCURLY                                                      # z3_conf
             | C2E2 LCURLY c2e2_configs? RCURLY                                                        # c2e2_conf
             | SPACEEX LCURLY spaceex_configs? RCURLY                                               # spaceex_conf
             | SSMT LCURLY ssmt_configs? RCURLY                                                 # ssmt_conf
               ;

flowstar_configs: flowstar_config+;
yices_configs: yices_config+;
z3_configs: z3_config+;
c2e2_configs: c2e2_config+;
spaceex_configs: spaceex_config+;
ssmt_configs: ssmt_config+;

z3_config: LOGIC QUOTE VALUE QUOTE                                                                  # z3_logic;
yices_config: LOGIC QUOTE VALUE QUOTE                                                                # yices_logic;
ssmt_config: LOGIC QUOTE VALUE QUOTE                                                                # ssmt_logic;
c2e2_config: FS_FIXED_STEPS NUMBER                                                      # c2e2_fixed_step
            | TIME NUMBER                                                            # c2e2_time
            | KVALUE NUMBER                                                          # c2e2_kvalue;

spaceex_config: TIME NUMBER                     # spaceex_time
            |   FS_FIXED_STEPS NUMBER           # spaceex_fixed_step
            |   MAX_DIS_COMP    NUMBER          # spaceex_max_discrete_computation
            |   REL_ERR NUMBER1                  # spaceex_rel_err
            |   ABS_ERR NUMBER1                  # spaceex_abs_err
            ;


flowstar_variable_list: VALUE                                                                           # fs_single_value_list
                | VALUE COMMA VALUE                                                                     # fs_single_pair_value_list
                ;

flowstar_config: FS_FIXED_STEPS NUMBER                                                   # fs_fixed_step
               | TIME NUMBER                                                          # fs_time
               | FS_REMAINDER_ESTI NUMBER1                                    # fs_remainder
               | FS_ID_PRECOND                                                                          # fs_id_precond
               | FS_GNUPLOT_OCTAGON flowstar_variable_list+                                             # fs_gnuplot_octagon
               | FS_ADAPTIVE_ORDER LCURLY 'min' NUMBER COMMA 'max' NUMBER RCURLY         # fs_adaptive_order
               | FS_CUT_OFF NUMBER1                                           # fs_cutoff
               | FS_PRECISION NUMBER                                                     # fs_precision
               | FS_NO_OUTPUT                                                                           # fs_no_output
               | FS_MAX_JUMPS NUMBER                                                     # fs_max_jumps
               ;

 
