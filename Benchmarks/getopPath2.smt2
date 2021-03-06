(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :status sat)
(declare-fun c0 () (_ BitVec 8))
(declare-fun c1 () (_ BitVec 8))
(declare-fun c2 () (_ BitVec 8))
(assert (or (= c0 #x20) (= c0 #x09) (= c0 #x0A)))
(assert (not (or (= c1 #x20) (= c1 #x09) (= c1 #x0A))))
(assert (not (and (distinct c1 #x2E) (or (bvult c1 #x30) (bvugt c1 #x39)))))
(assert (not (and (bvuge c2 #x30) (bvule c2 #x39))))
(assert (not (= c2 #x2E)))
(check-sat)
(exit)
