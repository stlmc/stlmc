import sys
sys.path.append("/home/rgyenr2/workspace/STL/")

from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings
from hylaa.core import Core
from hylaa.stateset import StateSet
from hylaa import lputil, symbolic
from hylaa.aggstrat import Aggregated


def make_automaton():
    'make the hybrid automaton'

    ha = HybridAutomaton('twoBatteryPoly')

    # variables
    variables = ["x1", "x2"]
    constant_dict = {"coeff_1": 0.015, "coeff_2": 0.045}

    ##### mode : false, false #####
    mode_ff = ha.new_mode("mode_ff")
    mode_ff_derivatives = ["-1 * coeff_1 * ((1 - 2 * 0.01) * x1 + 0.01 * x2)",
                           "-1 * coeff_2 * ((1 - 2 * 0.01) * x2 + 0.01 * x1)"]
    mode_ff_a_mat = symbolic.make_dynamics_mat(variables, mode_ff_derivatives, constant_dict, has_affine_variable=True)
    mode_ff.set_dynamics(mode_ff_a_mat)

    mode_ff_invariant = "x1 >= 0 & x2 >= 0"
    mode_ff_inv_mat, mode_ff_inv_rhs = symbolic.make_condition(variables, mode_ff_invariant.split('&'), constant_dict,
                                                               has_affine_variable=True)
    mode_ff.set_invariant(mode_ff_inv_mat, mode_ff_inv_rhs)

    ##### mode : false, true #####
    mode_ft = ha.new_mode("mode_ft")
    mode_ft_derivatives = ["-1 * coeff_1 * ((1 - 2 * 0.01) * x1 + 0.01 * x2)",
                           "coeff_2 * (200 - ((1 - 2 * 0.01) * x2 + 0.01 * x1))"]
    mode_ft_a_mat = symbolic.make_dynamics_mat(variables, mode_ft_derivatives, constant_dict, has_affine_variable=True)
    mode_ft.set_dynamics(mode_ft_a_mat)

    mode_ft_invariant = "x1 >= 0 & x2 <= 50"
    mode_ft_inv_mat, mode_ft_inv_rhs = symbolic.make_condition(variables, mode_ft_invariant.split('&'), constant_dict,
                                                               has_affine_variable=True)
    mode_ft.set_invariant(mode_ft_inv_mat, mode_ft_inv_rhs)

    ##### mode : true, false #####
    mode_tf = ha.new_mode("mode_tf")
    mode_tf_derivatives = ["coeff_1 * (100 - ((1 - 2 * 0.01) * x1 + 0.01 * x2))",
                           "-1 * coeff_2 * ((1 - 2 * 0.01) * x2 + 0.01 * x1)"]
    mode_tf_a_mat = symbolic.make_dynamics_mat(variables, mode_tf_derivatives, constant_dict, has_affine_variable=True)
    mode_tf.set_dynamics(mode_tf_a_mat)

    mode_tf_invariant = "x1 <= 50 & x2 >= 0"
    mode_tf_inv_mat, mode_tf_inv_rhs = symbolic.make_condition(variables, mode_tf_invariant.split('&'), constant_dict,
                                                               has_affine_variable=True)
    mode_tf.set_invariant(mode_tf_inv_mat, mode_tf_inv_rhs)

    ##### mode : true, true #####
    mode_tt = ha.new_mode("mode_tt")
    mode_tt_derivatives = ["coeff_1 * (100 - ((1 - 2 * 0.01) * x1 + 0.01 * x2))",
                           "coeff_2 * (200 - ((1 - 2 * 0.01) * x2 + 0.01 * x1))"]
    mode_tt_a_mat = symbolic.make_dynamics_mat(variables, mode_tt_derivatives, constant_dict, has_affine_variable=True)
    mode_tt.set_dynamics(mode_tt_a_mat)

    mode_tt_invariant = "x1 <= 50 & x2 <= 50"
    mode_tt_inv_mat, mode_tt_inv_rhs = symbolic.make_condition(variables, mode_tt_invariant.split('&'), constant_dict,
                                                               has_affine_variable=True)
    mode_tt.set_invariant(mode_tt_inv_mat, mode_tt_inv_rhs)

    # error mode
    error = ha.new_mode('error')

    mode_list = [mode_ff, mode_ft, mode_tf, mode_tt]

    # dst_mode, name, guard, reset
    # x1 >= ((x1 + x2) / 2 + 0.5) & x2 >= ((x1 + x2) / 2 + 0.5)
    total_list = [[(mode_ft, "ff -> ft", "x1 >= ((x1 + x2) / 2 + 0.5) & x2 <= ((x1 + x2) / 2 + 0.5)"),
                   (mode_tf, "ff -> tf", "x1 <= (x1 + x2) / 2 & x2 >= ((x1 + x2) / 2 + 0.5)"),
                   (mode_tt, "ff -> tt", "x1 <= (x1 + x2) / 2 & x2 <= (x1 + x2) / 2")],
                  [(mode_ff, "ft -> ff", "x1 >= 0.0 & x2 <= 33.0"),
                   (mode_tf, "ft -> tf", "x1 <= ((x1 + x2) / 2) & x2 >= ((x1 + x2) / 2 + 0.5)"),
                   (mode_tt, "ft -> tt", "x1 <= ((x1 + x2) / 2) & x2 <= ((x1 + x2) / 2)")],
                  [(mode_ff, "tf -> ff", "x1 >= ((x1 + x2) / 2) + 0.5 & x2 >= ((x1 + x2) / 2 + 0.5)"),
                   (mode_ft, "tf -> ft", "x1 >= ((x1 + x2) / 2) + 0.5 & x2 <= ((x1 + x2) / 2)"),
                   (mode_tt, "tf -> tt", "x1 <= ((x1 + x2) / 2) & x2 <= ((x1 + x2) / 2)")],
                  [(mode_ff, "tt -> ff", "x1 >= ((x1 + x2) / 2) + 0.5 & x2 >= ((x1 + x2) / 2 + 0.5)"),
                   (mode_ft, "tt -> ft", "x1 >= ((x1 + x2) / 2) + 0.5 & x2 <= ((x1 + x2) / 2)"),
                   (mode_tf, "tt -> tf", "x1 <= ((x1 + x2) / 2) & x2 >= ((x1 + x2) / 2) + 0.5")]]

    error_guard = "x1 >= 22.5"

    ############## Transitions ##############
    for index, total in enumerate(total_list):
        for flag, (dst_mode, trans_name, trans_guard) in enumerate(total):
            src_mode = mode_list[index]
            if flag == 0:
                err_name = src_mode.name + "_err"
                print("add error transition : {}".format(err_name))
                trans_to_error = ha.new_transition(src_mode, error, err_name)
                error_mat, error_rhs = symbolic.make_condition(variables, error_guard.split('&'), constant_dict,
                                                               has_affine_variable=True)
                trans_to_error.set_guard(error_mat, error_rhs)

            print(trans_name)
            new_transition = ha.new_transition(src_mode, dst_mode, trans_name)
            mat, rhs = symbolic.make_condition(variables, trans_guard.split('&'), constant_dict,
                                               has_affine_variable=True)
            new_transition.set_guard(mat, rhs)

    return ha


def make_init(ha, box):
    'make the initial states'

    mode = ha.modes['mode(0)']
    # px==-0.0165 & py==0.003 & vx==0 & vy==0 & I==0 & affine==1.0
    init_lpi = lputil.from_box(box, mode)
    init_list = [StateSet(init_lpi, mode)]

    return init_list


def make_settings():
    'make the reachability settings object'

    # see hylaa.settings for a list of reachability settings
    settings = HylaaSettings(0.1, 100)  # step: 0.001, bound: 0.1

    # settings.stop_on_aggregated_error = False

    # settings.aggstrat = MyAggergated()
    settings.aggstrat.deaggregate = True  # use deaggregation
    settings.aggstrat.deagg_preference = Aggregated.DEAGG_LEAVES_FIRST

    settings.stdout = HylaaSettings.STDOUT_VERBOSE
    return settings


def run_hylaa():
    'main entry point'

    ha = make_automaton()

    box = [(19.9, 20.1), (19.9, 20.1), (1.0, 1.0)]

    settings = make_settings()

    result = Core(ha, settings).run(make_init(ha, box))

    if result.counterexample:
        print(f"counterexample : {result.counterexample}")


if __name__ == "__main__":
    run_hylaa()
