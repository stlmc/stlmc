(set-logic QF_NRA)
(declare-fun x1 () Real)
;(declare-fun x2 () Real)
(declare-fun t () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
;(assert (and (>= x1 x2) (<= x1 (+ x2 10.0))))
;(assert
;  (or (and (> x1 0.0) (< x1 10.0)) (forall ()
;   (and (>= (* (sin x1) 1) 0.5) (= t true)
;   ))))
(assert
(and (= t1 0) (= t2 2))
)
(assert
(and (> x1 -2) (< x1 3))
)



(set-logic QF_NRA)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(assert
    (and (= t1 0) (> t2 2) (< t2 3))
)
(assert
    (forall ((x Real [t1, t2])) (> x 0))
)
(check-sat)
(get-model)
(exit)









;f_sat = logical_and(y > 0, x > 0, forall(vars, logical_and(logical_or(y > 1, y < 10), x < 10, x > 11)))
;(assert
; (and (> x2 0.0) (> x1 0.0)
;  (forall () (and (or (> x2 1.0) (< x2 10.0)) (< x1 10.0) (> x1 11.0))
;  )
; )
;)
(check-sat)
(get-model)
(exit)

 let
 ((a (+ 6 5)))

 (= 0 (- a 11))