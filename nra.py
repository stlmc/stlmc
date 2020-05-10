#! /usr/bin/env python

from yices import *


cfg = Config()
cfg.default_config_for_logic('QF_NRA')
ctx = Context(cfg)

real_t = Types.real_type()
x = Terms.new_uninterpreted_term(real_t, 'x')
y = Terms.new_uninterpreted_term(real_t, 'y')

fmla0 = Terms.parse_term('(= (+ (* x x) (* y y)) 1)')
fmla1 = Terms.parse_term('(= x (* 2 y))')
fmla2 = Terms.parse_term('(> x 0)')

ctx.assert_formulas([fmla0, fmla1, fmla2])

status = ctx.check_context()

if status == Status.SAT:
    model = Model.from_context(ctx, 1)
    model_string = model.to_string(80, 100, 0)
    print(model_string)
    xval = model.get_value(x)
    yval = model.get_value(y)
    print('x = {0}, y = {1}'.format(xval, yval))

cfg.dispose()
ctx.dispose()
Yices.exit()
