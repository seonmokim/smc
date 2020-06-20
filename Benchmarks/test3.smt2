(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(assert (= b (_ bv255 8)))
(assert (= c (_ bv255 8)))
(assert (= d (bvadd b c)))

(check-sat)
(get-model)

