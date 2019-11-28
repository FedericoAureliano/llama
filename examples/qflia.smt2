(set-logic QF_LIA)
(declare-fun x () Int)
(assert (and (= (+ x 7) x) (> x 7)))
(check-sat)