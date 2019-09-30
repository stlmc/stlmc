(assert
 (and ((- 20.0) <= x1_0_t <= 100) 
      (-20 <= x1_1_t <= 100.0) 
       (not a_0) 
       (19.9 <= x1_0_0 <= 20.1) 
       (or (and (not (= 1 currentMode_0)) (= 0 currentMode_0) (not a_0) (= x1_0_t (+ (* (- (/ 1.0 25.0)) (* time0 time0)) x1_0_0))) 
                (and (not (= 0 currentMode_0)) (= 1 currentMode_0) a_0 (= x1_0_t (+ (* (/ 1.0 25.0) (* time0 time0)) time0 x1_0_0)))) 
       (or (and (not (= 1 currentMode_1)) (= 0 currentMode_1) (not a_1)) (= x1_1_t (+ (* (- (/ 1.0 25.0)) (* time1 time1)) x1_1_0)))
                (and (not (= 0 currentMode_1)) $x57 a_1 (= x1_1_t (+ (* (/ 1.0 25.0) (* time1 time1)) time1 x1_1_0)))) 
       (or (and (not a_0) (or (and (not (<= x1_0_t 26.0)) (not a_1) (= x1_1_0 x1_0_t)) 
                                      (and (>= 24.0 x1_0_t) a_1 (= x1_1_0 x1_0_t))) 
                 (and a_0 (or (and (not (<= x1_0_t 26.0)) (not a_1) (= x1_1_0 x1_0_t)) 
                                      (and (>= 24.0 x1_0_t) a_1 (= x1_1_0 x1_0_t)))))) 
       (or (and (not a_1) (or (and (not (<= x1_1_t 26.0)) (not a_2) (= x1_2_0 x1_1_t)) 
                                      (and (>= 24.0 x1_1_t) a_2 (= x1_2_0 x1_1_t)))) 
                 (and a_1 (or (and (not (<= x1_1_t 26.0)) (not a_2) (= x1_2_0 x1_1_t)) 
                                      (and (>= 24.0 x1_1_t) a_2 (= x1_2_0 x1_1_t)))))
  



(<= 0.0 tau_0) (= time0 tau_0) (= time1 (+ tau_1 (* (- 1.0) tau_0))) (not (<= tau_1 tau_0)))
 )
 )
 )
 )
 )
 )
 )
 )
 )
 )
 )
 ))



