(set-logic QF_BV)
(declare-fun xA () (_ BitVec 2))
(declare-fun xB () (_ BitVec 2))
(declare-fun xC () (_ BitVec 2))
(declare-fun xD () (_ BitVec 2))
(declare-fun xE () (_ BitVec 2))
(declare-fun xF () (_ BitVec 2))
(declare-fun xG () (_ BitVec 2))
(declare-fun xH () (_ BitVec 2))
(assert (distinct xA xB))
(assert (distinct xA xD))
(assert (distinct xB xC))
(assert (distinct xB xD))
(assert (distinct xB xE))
(assert (distinct xC xE))
(assert (distinct xD xE))
(assert (distinct xD xF))
(assert (distinct xD xG))
(assert (distinct xE xG))
(assert (distinct xE xH))
(assert (distinct xF xG))
(assert (distinct xG xH))
(check-sat)
(exit)