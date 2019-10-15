#! /usr/bin/env python

from yices import *


cfg = Config()
cfg.default_config_for_logic('QF_LRA')
ctx = Context(cfg)

real_t = Types.real_type()
x = Terms.new_uninterpreted_term(real_t, 'x_0_0')
x = Terms.new_uninterpreted_term(real_t, 'x_0_t')
x = Terms.new_uninterpreted_term(real_t, 'x_1_0')
x = Terms.new_uninterpreted_term(real_t, 'x_1_t')

fmla0 = Terms.parse_term('(and (and (> x_0_0 20.0) (<= x_0_0 100.0)) (and (> x_0_t 20.0) (<= x_0_t 100.0)) (and (> x_1_0 20.0) (<= x_1_0 100.0)) (and (> x_1_t 20.0) (<= x_1_t 100.0)))')

ctx.assert_formulas([fmla0])
status = ctx.check_context()

if status == Status.SAT:
    model = Model.from_context(ctx, 1)
    model_string = model.to_string(80, 100, 0)
    print(model_string)

cfg.dispose()
ctx.dispose()
Yices.exit()
