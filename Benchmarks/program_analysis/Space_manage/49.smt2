(set-logic QF_BV)
(declare-fun Atti_absqBT () (_ BitVec 8))
(declare-fun Changeable_qUL () (_ BitVec 8))
(declare-fun DeltaT () (_ BitVec 8))
(declare-fun Flg_BZ5 () (_ BitVec 8))
(declare-fun Flg_ZT11 () (_ BitVec 8))
(declare-fun OrbitCmd_Tgon () (_ BitVec 8))
(declare-fun Time_T () (_ BitVec 8))
(declare-fun TkCount_TjsumX () (_ BitVec 8))
(declare-fun TkCount_TjsumY () (_ BitVec 8))
(declare-fun TkCount_TjsumZ () (_ BitVec 8))
(declare-fun temp1 () (_ BitVec 8))
(declare-fun temp2 () (_ BitVec 8))
(declare-fun tmpT () (_ BitVec 8))
(assert(and (bvsgt OrbitCmd_Tgon (_ bv0 8))
     (bvsge Time_T OrbitCmd_Tgon)
     (bvsle Time_T (bvadd OrbitCmd_Tgon (_ bv16 8)))))
(assert(not (bvsge Atti_absqBT Changeable_qUL)))
(assert(not (bvsge DeltaT tmpT)))
(assert(or (= Flg_BZ5 (_ bv0 8)) (= Flg_BZ5 (_ bv3 8)) (= Flg_BZ5 (_ bv5 8)) (= Flg_BZ5 (_ bv10 8)) (= Flg_BZ5 (_ bv15 8))))
(assert(or (bvsgt TkCount_TjsumY temp1) (bvsgt TkCount_TjsumZ temp1) (bvsgt TkCount_TjsumX temp2)))
(assert(not (= Flg_ZT11 (_ bv1 8))))
