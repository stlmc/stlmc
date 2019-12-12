(set-logic QF_NRA)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun t () Real)
;(assert
;    (and (= t1 0) (> t2 2) (< t2 3))
;)
;(assert
 ;   (=> (forall ((x Real)) (> (+ x t) 0)) (> t 0))
;)
(assert
    (forall () true)
)
(check-sat)
(get-model)
(exit)
