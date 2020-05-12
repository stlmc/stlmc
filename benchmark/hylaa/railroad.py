'''
Linear Railroad Model from Hylaa
'''

from matplotlib import collections

from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings, PlotSettings, LabelSettings
from hylaa.core import Core
from hylaa.aggstrat import Aggregated
from hylaa.stateset import StateSet
from hylaa import lputil

def make_automaton():
    'make the hybrid automaton'

    ha = HybridAutomaton('Linear Railroad Example')
    # [tx, bx]

    # tx' = -5, bx' = 0
    m1 = ha.new_mode('far')
    m1.set_dynamics([[0, 0, -5], [0, 0, 0], [0, 0, 0]])
    m1.set_invariant([[-1, 0, 0]], [0]) # tx >= 0

    # tx' == -5, bx' = 5
    m2 = ha.new_mode('approach')
    m2.set_dynamics([[0, 0, -5], [0, 0, 5], [0, 0, 0]])

    # tx' == -5, bx' = 10
    m3 = ha.new_mode('near')
    m3.set_dynamics([[0, 0, -5], [0, 0, 10], [0, 0, 0]])

    # tx' = -5, bx' = -5
    m4 = ha.new_mode('past')
    m4.set_dynamics([[0, 0, -5], [0, 0, -5], [0, 0, 0]])
    m4.set_invariant([-1, 0, 0], [0]) # tx >= 0    

    t = ha.new_transition(m1, m2)
    # 35 <= tx < 50
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0]]
    guard_rhs = [-35, 50]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m1, m3)
    # 5 <= tx < 35
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.]]
    guard_rhs = [-5, 35]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m1, m4)
    # -5 <= tx < 5, bx <= 80
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.], \
            [0, 1, 0]]
    guard_rhs = [5, 5, 80]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m1, m2)
    # 35 <= tx < 50
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0]]
    guard_rhs = [-35, 50]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m1, m3)
    # 5 <= tx < 35
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.]]
    guard_rhs = [-5, 35]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m1, m1)
    # tx < -5, bx > 85
    guard_mat = [\
            [1.0, 0., 0.], \
            [-0, -1, -0]]
    guard_rhs = [-5, -85]
    t.set_guard(guard_mat, guard_rhs)

    # bx' = bx, tx' = tx + 100
    reset_csr = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]

    minkowski_csr = [[1], [0], [0]]
    constraints_csr = [[1], [-1]]
    constraints_rhs = [100, -100]
    t.set_reset(reset_csr, minkowski_csr, constraints_csr, constraints_rhs)


    # mode2
    t = ha.new_transition(m2, m4)
    # -5 <= tx < 5, bx <= 80
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.], \
            [0, 1, 0]]
    guard_rhs = [5, 5, 80]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m2, m2)
    # 35 <= tx < 50
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0]]
    guard_rhs = [-35, 50]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m2, m3)
    # 5 <= tx < 35
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.]]
    guard_rhs = [-5, 35]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m2, m1)
    # tx < -5, bx > 85
    guard_mat = [\
            [1.0, 0., 0.], \
            [-0, -1, -0]]
    guard_rhs = [-5, -85]
    t.set_guard(guard_mat, guard_rhs)

    # bx' = bx, tx' = tx + 100
    reset_csr = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]

    minkowski_csr = [[1], [0], [0]]
    constraints_csr = [[1], [-1]]
    constraints_rhs = [100, -100]
    t.set_reset(reset_csr, minkowski_csr, constraints_csr, constraints_rhs)

    # mode3

    t = ha.new_transition(m3, m4)
    # -5 <= tx < 5, bx <= 80
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.], \
            [0, 1, 0]]
    guard_rhs = [5, 5, 80]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m3, m2)
    # 35 <= tx < 50
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0]]
    guard_rhs = [-35, 50]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m3, m3)
    # 5 <= tx < 35
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.]]
    guard_rhs = [-5, 35]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m3, m1)
    # tx < -5, bx > 85
    guard_mat = [\
            [1.0, 0., 0.], \
            [-0, -1, -0]]
    guard_rhs = [-5, -85]
    t.set_guard(guard_mat, guard_rhs)

    # bx' = bx, tx' = tx + 100
    reset_csr = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]

    minkowski_csr = [[1], [0], [0]]
    constraints_csr = [[1], [-1]]
    constraints_rhs = [100, -100]
    t.set_reset(reset_csr, minkowski_csr, constraints_csr, constraints_rhs)

    # mode 4

    t = ha.new_transition(m4, m4)
    # -5 <= tx < 5, bx <= 80
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.], \
            [0, 1, 0]]
    guard_rhs = [5, 5, 80]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m4, m2)
    # 35 <= tx < 50
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0]]
    guard_rhs = [-35, 50]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m4, m3)
    # 5 <= tx < 35
    guard_mat = [\
            [-1.0, 0., 0.], \
            [1.0 , -0, -0.]]
    guard_rhs = [-5, 35]
    t.set_guard(guard_mat, guard_rhs)

    t = ha.new_transition(m4, m1)
    # tx < -5, bx > 85
    guard_mat = [\
            [1.0, 0., 0.], \
            [-0, -1, -0]]
    guard_rhs = [-5, -85]
    t.set_guard(guard_mat, guard_rhs)

    # bx' = bx, tx' = tx + 100
    reset_csr = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]

    minkowski_csr = [[1], [0], [0]]
    constraints_csr = [[1], [-1]]
    constraints_rhs = [100, -100]
    t.set_reset(reset_csr, minkowski_csr, constraints_csr, constraints_rhs)

    '''
    t = ha.new_transition(m2, m3)
    t.set_guard_true()

    error = ha.new_mode('error')
    t = ha.new_transition(m3, error)

    unsafe_rhs = [-unsafe_box[0][0], unsafe_box[0][1], -unsafe_box[1][0], unsafe_box[1][1]]
    
    # x >= 1.1 x <= 1.9, y >= 2.7, y <= 4.3
    t.set_guard([[-1, 0, 0], [1, 0, 0], [0, -1, 0], [0, 1, 0]], unsafe_rhs)

    t = ha.new_transition(m2, error)
    # x >= 1.1 x <= 1.9, y >= 2.7, y <= 4.3
    t.set_guard([[-1, 0, 0], [1, 0, 0], [0, -1, 0], [0, 1, 0]], unsafe_rhs) 
    '''
    
    return ha

def make_init(ha):
    'make the initial states'

    mode = ha.modes['far']
    init_lpi = lputil.from_box([(85, 90), (0, 1), (1.0, 1.0)], mode)
    
    init_list = [StateSet(init_lpi, mode)]

    return init_list

def make_settings():
    'make the reachability settings object'

    # see hylaa.settings for a list of reachability settings
    # step_size = 0.1, max_time = 10
    settings = HylaaSettings(0.1, 10)
    settings.plot.plot_mode = PlotSettings.PLOT_IMAGE
    settings.stdout = HylaaSettings.STDOUT_VERBOSE
    settings.plot.filename = "demo_reset.png"

    return settings

def run_hylaa():
    'main entry point'

   # unsafe_box = [[5.1, 5.9], [4.1, 4.9]]

    ha = make_automaton()

    init_states = make_init(ha)

    settings = make_settings()

    Core(ha, settings).run(init_states)

if __name__ == "__main__":
    run_hylaa()
