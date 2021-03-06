(set-logic QF_BV)
(declare-fun day () (_ BitVec 5))
(declare-fun month () (_ BitVec 4))
(declare-fun year () (_ BitVec 12))
(assert (bvslt year (_ bv0 12)))
(assert (not (or (bvsle month (_ bv0 4)) (bvsgt month (_ bv12 4)) (bvsle day (_ bv0 5)) (bvsgt day (_ bv31 5)))))
(assert (not (bvsgt month (_ bv2 4))))
(assert (not (= year (_ bv1582 12))))
(assert (not (bvslt month (_ bv10 4))))
(assert (and (= month (_ bv10 4)) (bvslt day (_ bv15 5))))
(check-sat)
