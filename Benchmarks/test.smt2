(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 4))
(declare-fun c () (_ BitVec 4))
(declare-fun d () (_ BitVec 4))
(assert (= a ((_ sign_extend 4) (bvor b (bvand c d)))))
