#!/usr/bin/env python


from yices.Types import Types

from yices.Terms import Terms

from yices.Config import Config

from yices.Context import Context

from yices.Status import Status

from yices.Model import Model

from yices.Yices import Yices



int_t = Types.int_type()


#seems logical to make the terms in a grid.
X = [None] * 9
for i in range(9):
    X[i] = [None] * 9
    for j in range(9):
        X[i][j] = Terms.new_uninterpreted_term(int_t)

#not real happy about the indexing going from 0 to 8, but
#isolating access via V could make it easier to go from 1 to 9
def V(vi, vj):
    return X[vi][vj]



#make the constants that we will need
C = {}
for i in range(1, 10):
    C[i] = Terms.integer(i)

one = C[1]
nine = C[9]


config = Config()
config.default_config_for_logic("QF_LIA")

context = Context(config)



# x is between 1 and 9
def between_1_and_9(x):
    return Terms.yand([Terms.arith_leq_atom(one, x), Terms.arith_leq_atom(x, nine)])

for i in range(9):
    for j in range(9):
        context.assert_formula(between_1_and_9(V(i, j)))


# All elements in a row must be distinct
for i in range(9):
    context.assert_formula(Terms.distinct([V(i, j) for j in range(9)]))


# All elements in a column must be distinct
for i in range(9):
    context.assert_formula(Terms.distinct([V(j, i) for j in range(9)]))

# All elements in each 3x3 square must be distinct
for k in range(3):
    for l in range(3):
        context.assert_formula(Terms.distinct([V(i + 3 * l, j + 3 * k) for i in range(3) for j in range(3)]))


#initial conditions (part of the UI)
def set_value(ctx, position, value):
    (row, column) = position
    assert row >= 1 and row <= 9
    assert column >= 1 and column <= 9
    assert value >= 1  and value <= 9
    ctx.assert_formula(Terms.arith_eq_atom(V(row - 1, column - 1), C[value]))


#
# Constraints:
#
#   -------------------------
#   |     2 |       | 7 6 8 |
#   | 4   7 |       | 5     |
#   |       | 8   7 |       |
#   -------------------------
#   |   5   |   1   |       |
#   |   2 8 |       | 4     |
#   | 3     |   4   |   7   |
#   -------------------------
#   |       | 3   1 |       |
#   |     9 |       | 8   5 |
#   | 6 7 1 |       | 2     |
#   -------------------------
#

set_value(context, (1, 3), 2)
set_value(context, (1, 7), 7)
set_value(context, (1, 8), 6)
set_value(context, (1, 9), 8)

set_value(context, (2, 1), 4)
set_value(context, (2, 3), 7)
set_value(context, (2, 7), 5)

set_value(context, (3, 4), 8)
set_value(context, (3, 6), 7)

set_value(context, (4, 2), 5)
set_value(context, (4, 5), 1)

set_value(context, (5, 2), 2)
set_value(context, (5, 3), 8)
set_value(context, (5, 7), 4)

set_value(context, (6, 1), 3)
set_value(context, (6, 5), 4)
set_value(context, (6, 8), 7)

set_value(context, (7, 4), 3)
set_value(context, (7, 6), 1)

set_value(context, (8, 3), 9)
set_value(context, (8, 7), 8)
set_value(context, (8, 9), 5)

set_value(context, (9, 1), 6)
set_value(context, (9, 2), 7)
set_value(context, (9, 3), 1)
set_value(context, (9, 7), 2)

#check sat

smt_stat = context.check_context(None)

if smt_stat != Status.SAT:
    print 'No solution: smt_stat = {0}\n'.format(smt_stat)
else:
    #print model
    model = Model.from_context(context, 1)
    for i in range(9):
        for j in range(9):
            val = model.get_value(V(i, j))
            print 'V({0}, {1}) = {2}'.format(i, j, val)
    model.dispose()

print 'Cleaning up\n'

context.dispose()
config.dispose()


Yices.exit()
