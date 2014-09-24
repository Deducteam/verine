(set-logic QF_UFLIA)
(declare-fun x () Int)
(assert (not (= x x)))
(check-sat)
