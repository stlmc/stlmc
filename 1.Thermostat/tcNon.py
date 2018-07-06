testcase = [
        "(<> [0.0,10.0] (pf \/ qf))",
        "(<> [0.0,10.0] (ps \/ qs))"
]
testcaseSTL = [
        "(<> [0.0,10.0] (proMF /\ proMS)",
        "(proMF -> <> [0.0, 5.0] (~ proMF))",
        "(ps -> <> [0.0, 5.0] qs)",
        "([0.0, 10.0] proMF -> pf)"
]



