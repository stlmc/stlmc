testcase = [
        "(<> [0.0,10.0] (pf \/ qf))",
        "(<> [0.0,10.0] (ps \/ qs))"
]
testcaseSTL = [
        "(<> [0.0,10.0] (promf /\ proms)", \
        "(promf -> <> [0.0, 5.0] (~ promf))",
        "(ps -> <> [0.0, 5.0] qs)",
        "([] [0.0, 10.0] promf)"
]



