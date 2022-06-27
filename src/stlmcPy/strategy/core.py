from functools import singledispatch
from typing import Dict, Set, List, Tuple

import z3

from stlmcPy.constraints.constraints import *
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.strategy import unit_split
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.util.logger import Logger


class Node:
    pass


class SmtNode(Node):
    def __init__(self, assignments, L, Gamma, Q, k, isclosed):
        # dict
        self.assignments: Dict[Variable, Constant] = assignments
        self.L: List[Formula] = L
        # stack
        self.Gamma: List[SmtNode] = Gamma
        # queue
        self.Q: List[SmtNode] = Q
        # current Node's depth
        self.k: int = k
        self.isclosed: bool = isclosed

    def __repr__(self):
        return "< Node | assignment: {}, queue: {}, depth: {} >".format(self.assignments, self.Q, self.k)


class Generator:
    def __init__(self, const):
        self.bound_info: Dict[int, Formula] = dict()
        for i, c in enumerate(const):
            self.bound_info[i] = c

        self._z3solver = Z3Solver()
        self._z3solver.append_logger(Logger())
        self.max_bound = len(const)

        self.first_node = SmtNode(self.bound_info[0], list(), list(), list(), 0, False)
        # self._z3solver.raw_push()
        # self._z3solver.raw_add(self.bound_info[0])

        # print(self.bound_info)
        # print (const)
        # print("-s-s-s-")
        #
        # max_bound = max_bound + 1
        # forall_bound_map: Dict[int, Set[Formula]] = dict()
        # integral_bound_map: Dict[int, Set[Formula]] = dict()
        # init = None
        # tau_bound_map: Dict[int, Set[Formula]] = dict()
        # reset_bound_map: Dict[int, Set[Formula]] = dict()
        # guard_bound_map: Dict[int, Set[Formula]] = dict()
        #
        # for i in range(2 * max_bound):
        #     forall_bound_map[i], integral_bound_map[i], init, tau_bound_map[i], reset_bound_map[i], guard_bound_map[
        #         i] = unit_split(small_clause(const), i)
        #
        # print("init : {}".format(init))
        #
        #
        # self.bound_info = dict()
        # init_const = And(list(init))
        # for i in range(max_bound):
        #     inv_set, flow_set, tau_set = forall_bound_map[i], integral_bound_map[i], tau_bound_map[i]
        #     inv_const, flow_const, tau_const = Or(list(inv_set)), Or(list(flow_set)), And(list(tau_set))
        #     if i == 0:
        #         self.bound_info[i] = And([init_const, inv_const, flow_const, tau_const])
        #         continue
        #
        #     reset_set, guard_set = reset_bound_map[i - 1], guard_bound_map[i - 1]
        #     reset_const, guard_const = Or(list(reset_set)), Or(list(guard_set))
        #
        #     self.bound_info[i] = And([inv_const, flow_const, tau_const, reset_const, guard_const])

    def backtrack(self, node: SmtNode):
        def _find_position(_Q: List[SmtNode], _node: SmtNode):
            assert _node in _Q
            for _l, _no in enumerate(_Q):
                # the actual data structure must be the same
                if _no is _node:
                    return _l

        node.isclosed = True
        if len(node.Gamma) == 0:
            return node, -1
        node_prime = node.Gamma[-1]
        loc = _find_position(node_prime.Q, node)
        return node_prime, loc + 1

    def _get_psi_as_children(self, index: int):
        children = list()
        for i in range(index):
            # TODO: should add goal conditions
            children.append(self.bound_info[i])
        return children

    def next(self, node: SmtNode, index: int) -> Tuple[SmtNode, int]:
        if node.isclosed or node.k >= self.max_bound:
            return self.backtrack(node)

        if index < len(node.Q):
            return node.Q[index], 0

        psi_T = BoolVal("True")
        j = 0

        counter = 1
        while j <= index:
            print("  next (iter: {}, psi_T: {}, index: ({}/{}))".format(counter, psi_T, j, index))
            if j == index:
                children = list()
                bound_formula = self._get_psi_as_children(node.k + 1)
                scenario_psi = [f for f in node.L]

                children.extend(bound_formula)
                children.extend(scenario_psi)
                children.append(psi_T)

                result, _ = self._z3solver.solve(And(children))

                print(result)
                if result is False:
                    assignments_prime = self._z3solver.make_assignment()
                    c_sat = select_sat_clause(assignments_prime, psi_T)
                    psi_assn = And([phi for phi in c_sat])
                    psi_T = And([psi_T, psi_assn])

                    assn = assignments_prime.get_assignments()

                    L_prime = node.L.copy()
                    L_prime.append(psi_T)

                    Gamma_prime = node.Gamma.copy()
                    Gamma_prime.append(node)

                    foo = list()
                    node_prime = SmtNode(assn, L_prime, Gamma_prime, foo, node.k + 1, False)
                    node.Q.append(node_prime)
                    # print("inside result {}".format(node))
                    # print("added {}".format(node_prime))
                    # print()
                    return node_prime, 0

                else:
                    print("    backtrack (iter: {})".format(counter))
                    return self.backtrack(node)
            else:
                if j < len(node.Q):
                    print("node Q: {}".format(node.Q))
                    node_j = node.Q[j]
                    phi_prime = None
                    if len(node_j.L) > 0:
                        phi_prime = node_j.L[-1]

                    if phi_prime is not None:
                        psi_T = And([psi_T, Not(phi_prime)])
                    j = j + 1
                    counter += 1
                else:
                    return node, j

    def dfs(self, node: SmtNode):

        # node_T should be reference version
        node_T = node
        i = 0
        counter = 1
        while True:
            print("iteration {}".format(counter))
            node_T, i = self.next(node_T, i)
            if node_T is not node and not node_T.isclosed:
                counter += 1
                continue
            else:
                break

        print("are we ok?")






        # counter = 0
        # # select possible set of scenarios
        # additional = self.bound_info[node.index + 1]
        # self._z3solver.raw_push()
        # self._z3solver.raw_add(additional)
        # node.add(additional)
        #
        # print(index)
        #
        # # TODO : update this part to use list
        # while counter <= index:
        #
        #     # first, solve it
        #     result = self._z3solver.raw_check()
        #     if result == z3.sat:
        #         assignment = self._z3solver.raw_model().get_assignments()
        #         children = list()
        #
        #         self._z3solver.raw_push()
        #         if counter == index:
        #             print("positive")
        #             for v in assignment:
        #                 children.append(Eq(v, assignment[v]))
        #             child_const = And(children)
        #             node.add(child_const)
        #             node.assignments = assignment
        #             self._z3solver.raw_add(child_const)
        #             return node
        #         else:
        #             print("??S?S?s")
        #             # negate assignment
        #             for v in assignment:
        #                 children.append(Neq(v, assignment[v]))
        #             child_const = And(children)
        #             node.add(child_const)
        #             self._z3solver.raw_add(child_const)
        #         counter += 1
        #     else:
        #         self._z3solver.raw_pop()
        #         # update const
        #         node.const = And([node.const, Not(additional)])
        # return node


@singledispatch
def small_clause(const: Constraint):
    return {const}


@small_clause.register(Not)
def _(const: Not):
    return small_clause(const.child)


@small_clause.register(And)
def _(const: And):
    result = set()
    for c in list(const.children):
        result = result.union(small_clause(c))
    return result


@small_clause.register(Or)
def _(const: Or):
    result = set()
    for c in list(const.children):
        result = result.union(small_clause(c))
    return result


@small_clause.register(Implies)
def _(const: Implies):
    result = set()
    result = result.union(small_clause(const.left))
    result = result.union(small_clause(const.right))
    return result


def select_sat_clause(assignments: Assignment, target_formula: Formula):
    c_sat = set()
    clause_set = small_clause(target_formula)
    for clause in clause_set:
        # assignments.eval must return something
        eval_result = assignments.eval(clause)
        assert eval_result is not None
        if eval_result:
            c_sat.add(clause)
    return c_sat