(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (and (= x y) (not (= y x))))
(check-sat)