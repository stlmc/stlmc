(set-logic QF_NRA)
(declare-fun x1 () Real)
(assert (and (>= x1 0.7) (<= x1 1)))
(assert
 (forall
 ()
   (>= (* (sin x1) 1) 0.5)))
(check-sat)
(get-model)
(exit)
