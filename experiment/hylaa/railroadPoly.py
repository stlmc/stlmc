import os
import sys

sys.path.append(os.getcwd())

from hylaa import lputil, symbolic
from hylaa.aggstrat import Aggregated
from hylaa.core import Core
from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings
from hylaa.stateset import StateSet


def make_automaton():
    'make the hybrid automaton'

    ha = HybridAutomaton('railroadPoly')

    # variables
    variables = ["m", "tx", "bx", "vx", "vacc", "gTimer"]

    # mode names
    mode_names = ["mode(0)", "mode(5)", "mode(10)", "mode(-5)"]

    # all modes' derivatives are the same
    derivatives = ["0", "-5", "vx", "vacc", "0", "1"]

    # no constant dict
    constant_dict = {}

    ############## Modes ##############
    for mode_name in mode_names:
        mode = ha.new_mode(mode_name)
        a_mat = symbolic.make_dynamics_mat(variables, derivatives, constant_dict, has_affine_variable=True)
        mode.set_dynamics(a_mat)

        invariant = "gTimer <= 60"
        inv_mat, inv_rhs = symbolic.make_condition(variables, invariant.split('&'), constant_dict, has_affine_variable=True)
        mode.set_invariant(inv_mat, inv_rhs)


    # error mode
    error = ha.new_mode('error')

    ############## Transition ##############
    # target_mode, guard, reset
    transition_list = [[("mode(5)", "40 <= tx & tx <= 50", ["5", "tx", "bx", "vx", "5", "gTimer"]),
                        ("mode(10)", "10 <= tx & tx <= 30", ["10", "tx", "bx", "vx", "10", "gTimer"]),
                        ("mode(-5)", "-5 <= tx & tx <= 0", ["-5", "tx", "bx", "vx", "-5", "gTimer"])],
                       [("mode(10)", "10 <= tx & tx <= 30", ["10", "tx", "bx", "vx", "10", "gTimer"]),
                        ("mode(-5)", "-5 <= tx & tx <= 0", ["-5", "tx", "bx", "vx", "-5", "gTimer"]),
                        ("mode(0)", "85 <= bx & tx <= -8", ["0", "100 + tx", "bx", "vx", "0", "gTimer"])],
                       [("mode(5)", "40 <= tx & tx <= 50", ["5", "tx", "bx", "vx", "5", "gTimer"]),
                        ("mode(-5)", "-5 <= tx & tx <= 0", ["-5", "tx", "bx", "vx", "-5", "gTimer"]),
                        ("mode(0)", "85 <= bx & tx <= -8", ["0", "100 + tx", "bx", "vx", "0", "gTimer"])],
                       [("mode(5)", "40 <= tx & tx <= 50", ["5", "tx", "bx", "vx", "5", "gTimer"]),
                        ("mode(10)", "10 <= tx & tx <= 30", ["10", "tx", "bx", "vx", "10", "gTimer"]),
                        ("mode(0)", "85 <= bx & tx <= -8", ["0", "100 + tx", "bx", "vx", "0", "gTimer"])]
                       ]

    goal = "vacc >= 10 & tx <= 10 & gTimer >= 59.9"

    for mode_num, transition_info_list in enumerate(transition_list):
        src_mode_name = mode_names[mode_num]
        src_mode = ha.modes[src_mode_name]
        for err_flag, (dst_mode_name, guard, reset) in enumerate(transition_info_list):
            if err_flag == 1:
                err_transition_name = "t_{}_err".format(src_mode_name)
                print("add transition : {}".format(err_transition_name))
                err_transition = ha.new_transition(src_mode, error, err_transition_name)
                err_mat, err_rhs = symbolic.make_condition(variables, goal.split('&'), constant_dict,
                                                           has_affine_variable=True)
                err_transition.set_guard(err_mat, err_rhs)
            dst_mode = ha.modes[dst_mode_name]
            transition_name = "t_{}_{}".format(src_mode_name, dst_mode_name)
            print("add transition : {}".format(transition_name))
            transition = ha.new_transition(src_mode, dst_mode, transition_name)
            mat, rhs = symbolic.make_condition(variables, guard.split('&'), constant_dict, has_affine_variable=True)
            transition.set_guard(mat, rhs)

            reset_mat = symbolic.make_reset_mat(variables, reset, constant_dict, has_affine_variable=True)
            transition.set_reset(reset_mat)

    return ha


def make_init(ha, box):
    'make the initial states'

    mode = ha.modes['mode(0)']
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

    # settings.stdout = HylaaSettings.STDOUT_VERBOSE
    return settings


def run_hylaa():
    'main entry point'

    ha = make_automaton()

    box = [(0, 0), (60, 70), (0, 1), (0, 0.1), (0, 0), (0, 0), (1.0, 1.0)]

    settings = make_settings()

    result = Core(ha, settings).run(make_init(ha, box))

    #if result.counterexample:
    #    print("counterexample : {}".format(result.counterexample))


if __name__ == "__main__":
    run_hylaa()
