(set-logic QF_LIA)
(set-info :source |
Older mathsat benchmarks.  Contact Mathsat group at http://mathsat.itc.it/ for
more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun AT0_PROC3_CS () Bool)
(declare-fun AT1_PROC5_X () Int)
(declare-fun AT1_PROC5_CS () Bool)
(declare-fun AT0_PROC1_X () Int)
(declare-fun AT0_ID0 () Bool)
(declare-fun AT1_PROC2_C () Bool)
(declare-fun AT0_ID1 () Bool)
(declare-fun AT1_PROC2_B () Bool)
(declare-fun AT0_ID2 () Bool)
(declare-fun AT1_PROC2_A () Bool)
(declare-fun AT0_ID3 () Bool)
(declare-fun AT0_PROC3_SW_CS_A_TAU () Bool)
(declare-fun AT0_ID4 () Bool)
(declare-fun AT0_ID5 () Bool)
(declare-fun AT1_PROC2_CS () Bool)
(declare-fun AT0_PROC4_X () Int)
(declare-fun AT0_PROC3_TAU () Bool)
(declare-fun AT1_PROC5_C () Bool)
(declare-fun AT0_PROC2_SW_C_B_TAU () Bool)
(declare-fun AT1_PROC5_B () Bool)
(declare-fun AT1_PROC5_A () Bool)
(declare-fun AT0_PROC4_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC1_C () Bool)
(declare-fun AT0_PROC1_B () Bool)
(declare-fun AT0_PROC1_A () Bool)
(declare-fun AT1_PROC3_X () Int)
(declare-fun AT0_PROC3_WAIT () Bool)
(declare-fun AT0_PROC2_CS () Bool)
(declare-fun AT0_PROC4_C () Bool)
(declare-fun AT0_PROC4_B () Bool)
(declare-fun AT1_ID0 () Bool)
(declare-fun AT0_PROC4_A () Bool)
(declare-fun AT1_ID1 () Bool)
(declare-fun AT1_ID2 () Bool)
(declare-fun AT1_ID3 () Bool)
(declare-fun AT1_ID4 () Bool)
(declare-fun AT1_ID5 () Bool)
(declare-fun AT0_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC5_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC5_CS () Bool)
(declare-fun AT0_PROC5_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC4_TAU () Bool)
(declare-fun AT0_PROC2_X () Int)
(declare-fun AT1_PROC3_CS () Bool)
(declare-fun AT0_PROC4_SW_A_B_TAU () Bool)
(declare-fun AT1_PROC3_C () Bool)
(declare-fun AT1_PROC3_B () Bool)
(declare-fun AT1_PROC3_A () Bool)
(declare-fun AT0_PROC5_X () Int)
(declare-fun AT1_PROC1_X () Int)
(declare-fun AT1_Z () Int)
(declare-fun AT0_PROC4_SW_B_C_TAU () Bool)
(declare-fun AT0_PROC2_C () Bool)
(declare-fun AT0_PROC2_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC2_B () Bool)
(declare-fun AT0_PROC2_A () Bool)
(declare-fun AT0_PROC3_SW_B_C_TAU () Bool)
(declare-fun AT0_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC1_CS () Bool)
(declare-fun AT0_PROC5_SW_A_B_TAU () Bool)
(declare-fun AT0_PROC4_WAIT () Bool)
(declare-fun AT0_PROC1_TAU () Bool)
(declare-fun AT0_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT1_PROC4_X () Int)
(declare-fun AT0_PROC4_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC1_WAIT () Bool)
(declare-fun AT0_PROC5_TAU () Bool)
(declare-fun AT0_PROC5_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC5_C () Bool)
(declare-fun AT0_PROC5_B () Bool)
(declare-fun AT0_PROC5_A () Bool)
(declare-fun AT0_PROC4_CS () Bool)
(declare-fun AT1_PROC1_C () Bool)
(declare-fun AT1_PROC1_B () Bool)
(declare-fun AT1_PROC4_CS () Bool)
(declare-fun AT1_PROC1_A () Bool)
(declare-fun AT0_PROC3_SW_A_B_TAU () Bool)
(declare-fun AT0_DELTA () Bool)
(declare-fun AT0_PROC5_SW_B_C_TAU () Bool)
(declare-fun AT0_PROC3_X () Int)
(declare-fun AT0_PROC2_SW_B_C_TAU () Bool)
(declare-fun AT1_PROC4_C () Bool)
(declare-fun AT1_PROC1_CS () Bool)
(declare-fun AT1_PROC4_B () Bool)
(declare-fun AT1_PROC4_A () Bool)
(declare-fun AT0_PROC3_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT0_PROC2_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC2_TAU () Bool)
(declare-fun AT1_PROC2_X () Int)
(declare-fun AT0_PROC4_SW_C_CS_TAU () Bool)
(declare-fun AT0_Z () Int)
(declare-fun AT0_PROC5_WAIT () Bool)
(declare-fun AT0_PROC2_SW_A_B_TAU () Bool)
(declare-fun AT0_PROC3_C () Bool)
(declare-fun AT0_PROC3_B () Bool)
(declare-fun AT0_PROC3_A () Bool)
(declare-fun AT0_PROC3_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC2_WAIT () Bool)
(declare-fun AT0_PROC1_SW_B_C_TAU () Bool)
(assert (let ((?v_0 (not AT0_PROC1_A)) (?v_1 (not AT0_PROC1_B)) (?v_2 (not AT0_PROC1_C)) (?v_3 (not AT0_PROC1_CS)) (?v_4 (not AT1_PROC1_A)) (?v_5 (not AT1_PROC1_B)) (?v_6 (not AT1_PROC1_C)) (?v_7 (not AT1_PROC1_CS)) (?v_8 (not AT0_PROC2_A)) (?v_9 (not AT0_PROC2_B)) (?v_10 (not AT0_PROC2_C)) (?v_11 (not AT0_PROC2_CS)) (?v_12 (not AT1_PROC2_A)) (?v_13 (not AT1_PROC2_B)) (?v_14 (not AT1_PROC2_C)) (?v_15 (not AT1_PROC2_CS)) (?v_16 (not AT0_PROC3_A)) (?v_17 (not AT0_PROC3_B)) (?v_18 (not AT0_PROC3_C)) (?v_19 (not AT0_PROC3_CS)) (?v_20 (not AT1_PROC3_A)) (?v_21 (not AT1_PROC3_B)) (?v_22 (not AT1_PROC3_C)) (?v_23 (not AT1_PROC3_CS)) (?v_24 (not AT0_PROC4_A)) (?v_25 (not AT0_PROC4_B)) (?v_26 (not AT0_PROC4_C)) (?v_27 (not AT0_PROC4_CS)) (?v_28 (not AT1_PROC4_A)) (?v_29 (not AT1_PROC4_B)) (?v_30 (not AT1_PROC4_C)) (?v_31 (not AT1_PROC4_CS)) (?v_32 (not AT0_PROC5_A)) (?v_33 (not AT0_PROC5_B)) (?v_34 (not AT0_PROC5_C)) (?v_35 (not AT0_PROC5_CS)) (?v_36 (not AT1_PROC5_A)) (?v_37 (not AT1_PROC5_B)) (?v_38 (not AT1_PROC5_C)) (?v_39 (not AT1_PROC5_CS)) (?v_40 (= AT0_PROC1_X AT0_Z)) (?v_41 (> AT0_PROC1_X AT0_Z))) (let ((?v_122 (not ?v_40)) (?v_42 (= AT1_PROC1_X AT1_Z)) (?v_43 (> AT1_PROC1_X AT1_Z))) (let ((?v_121 (not ?v_42)) (?v_44 (= AT0_PROC2_X AT0_Z)) (?v_45 (> AT0_PROC2_X AT0_Z))) (let ((?v_127 (not ?v_44)) (?v_46 (= AT1_PROC2_X AT1_Z)) (?v_47 (> AT1_PROC2_X AT1_Z))) (let ((?v_126 (not ?v_46)) (?v_48 (= AT0_PROC3_X AT0_Z)) (?v_49 (> AT0_PROC3_X AT0_Z))) (let ((?v_131 (not ?v_48)) (?v_50 (= AT1_PROC3_X AT1_Z)) (?v_51 (> AT1_PROC3_X AT1_Z))) (let ((?v_130 (not ?v_50)) (?v_52 (= AT0_PROC4_X AT0_Z)) (?v_53 (> AT0_PROC4_X AT0_Z))) (let ((?v_135 (not ?v_52)) (?v_54 (= AT1_PROC4_X AT1_Z)) (?v_55 (> AT1_PROC4_X AT1_Z))) (let ((?v_134 (not ?v_54)) (?v_56 (= AT0_PROC5_X AT0_Z)) (?v_57 (> AT0_PROC5_X AT0_Z))) (let ((?v_139 (not ?v_56)) (?v_58 (= AT1_PROC5_X AT1_Z)) (?v_59 (> AT1_PROC5_X AT1_Z))) (let ((?v_138 (not ?v_58)) (?v_65 (- AT0_PROC1_X AT0_Z))) (let ((?v_62 (<= ?v_65 10)) (?v_73 (- AT0_PROC2_X AT0_Z))) (let ((?v_70 (<= ?v_73 10)) (?v_80 (- AT0_PROC3_X AT0_Z))) (let ((?v_77 (<= ?v_80 10)) (?v_87 (- AT0_PROC4_X AT0_Z))) (let ((?v_84 (<= ?v_87 10)) (?v_94 (- AT0_PROC5_X AT0_Z))) (let ((?v_91 (<= ?v_94 10)) (?v_60 (not AT0_PROC1_SW_A_B_TAU)) (?v_61 (not AT0_PROC1_SW_B_C_TAU)) (?v_63 (not AT0_PROC1_SW_C_B_TAU)) (?v_64 (not AT0_PROC1_SW_C_CS_TAU)) (?v_97 (= AT1_PROC1_X AT0_PROC1_X)) (?v_66 (not AT0_PROC1_SW_CS_A_TAU)) (?v_67 (= AT1_Z AT0_Z)) (?v_68 (not AT0_PROC2_SW_A_B_TAU)) (?v_69 (not AT0_PROC2_SW_B_C_TAU)) (?v_71 (not AT0_PROC2_SW_C_B_TAU)) (?v_72 (not AT0_PROC2_SW_C_CS_TAU)) (?v_99 (= AT1_PROC2_X AT0_PROC2_X)) (?v_74 (not AT0_PROC2_SW_CS_A_TAU)) (?v_75 (not AT0_PROC3_SW_A_B_TAU)) (?v_76 (not AT0_PROC3_SW_B_C_TAU)) (?v_78 (not AT0_PROC3_SW_C_B_TAU)) (?v_79 (not AT0_PROC3_SW_C_CS_TAU)) (?v_101 (= AT1_PROC3_X AT0_PROC3_X)) (?v_81 (not AT0_PROC3_SW_CS_A_TAU)) (?v_82 (not AT0_PROC4_SW_A_B_TAU)) (?v_83 (not AT0_PROC4_SW_B_C_TAU)) (?v_85 (not AT0_PROC4_SW_C_B_TAU)) (?v_86 (not AT0_PROC4_SW_C_CS_TAU)) (?v_103 (= AT1_PROC4_X AT0_PROC4_X)) (?v_88 (not AT0_PROC4_SW_CS_A_TAU)) (?v_89 (not AT0_PROC5_SW_A_B_TAU)) (?v_90 (not AT0_PROC5_SW_B_C_TAU)) (?v_92 (not AT0_PROC5_SW_C_B_TAU)) (?v_93 (not AT0_PROC5_SW_C_CS_TAU)) (?v_105 (= AT1_PROC5_X AT0_PROC5_X)) (?v_95 (not AT0_PROC5_SW_CS_A_TAU)) (?v_96 (not AT0_PROC1_WAIT)) (?v_107 (not AT0_PROC1_TAU)) (?v_98 (not AT0_PROC2_WAIT)) (?v_108 (not AT0_PROC2_TAU)) (?v_100 (not AT0_PROC3_WAIT)) (?v_110 (not AT0_PROC3_TAU)) (?v_102 (not AT0_PROC4_WAIT)) (?v_111 (not AT0_PROC4_TAU)) (?v_104 (not AT0_PROC5_WAIT)) (?v_112 (not AT0_PROC5_TAU)) (?v_106 (not AT0_DELTA)) (?v_118 (< AT1_Z AT0_Z))) (let ((?v_109 (or ?v_106 ?v_118)) (?v_113 (< AT1_PROC1_X AT0_PROC1_X)) (?v_119 (not ?v_97)) (?v_114 (< AT1_PROC2_X AT0_PROC2_X)) (?v_125 (not ?v_99)) (?v_115 (< AT1_PROC3_X AT0_PROC3_X)) (?v_129 (not ?v_101)) (?v_116 (< AT1_PROC4_X AT0_PROC4_X)) (?v_133 (not ?v_103)) (?v_117 (< AT1_PROC5_X AT0_PROC5_X)) (?v_137 (not ?v_105)) (?v_120 (not ?v_67)) (?v_124 (not ?v_118))) (let ((?v_123 (or ?v_122 ?v_119)) (?v_128 (or ?v_127 ?v_125)) (?v_132 (or ?v_131 ?v_129)) (?v_136 (or ?v_135 ?v_133)) (?v_140 (or ?v_139 ?v_137)) (?v_141 (not AT0_ID0)) (?v_142 (not AT0_ID1)) (?v_143 (not AT0_ID2)) (?v_144 (not AT0_ID3)) (?v_145 (not AT0_ID4)) (?v_146 (not AT0_ID5)) (?v_147 (not AT1_ID0)) (?v_148 (not AT1_ID1)) (?v_149 (not AT1_ID2)) (?v_150 (not AT1_ID3)) (?v_151 (not AT1_ID4)) (?v_152 (not AT1_ID5)) (?v_153 (- AT1_PROC1_X AT1_Z)) (?v_154 (- AT1_PROC2_X AT1_Z)) (?v_155 (- AT1_PROC3_X AT1_Z)) (?v_156 (- AT1_PROC4_X AT1_Z)) (?v_157 (- AT1_PROC5_X AT1_Z))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_0 ?v_1) (or ?v_0 ?v_2)) (or ?v_0 ?v_3)) (or ?v_1 ?v_2)) (or ?v_1 ?v_3)) (or ?v_2 ?v_3)) (or ?v_4 ?v_5)) (or ?v_4 ?v_6)) (or ?v_4 ?v_7)) (or ?v_5 ?v_6)) (or ?v_5 ?v_7)) (or ?v_6 ?v_7)) (or ?v_8 ?v_9)) (or ?v_8 ?v_10)) (or ?v_8 ?v_11)) (or ?v_9 ?v_10)) (or ?v_9 ?v_11)) (or ?v_10 ?v_11)) (or ?v_12 ?v_13)) (or ?v_12 ?v_14)) (or ?v_12 ?v_15)) (or ?v_13 ?v_14)) (or ?v_13 ?v_15)) (or ?v_14 ?v_15)) (or ?v_16 ?v_17)) (or ?v_16 ?v_18)) (or ?v_16 ?v_19)) (or ?v_17 ?v_18)) (or ?v_17 ?v_19)) (or ?v_18 ?v_19)) (or ?v_20 ?v_21)) (or ?v_20 ?v_22)) (or ?v_20 ?v_23)) (or ?v_21 ?v_22)) (or ?v_21 ?v_23)) (or ?v_22 ?v_23)) (or ?v_24 ?v_25)) (or ?v_24 ?v_26)) (or ?v_24 ?v_27)) (or ?v_25 ?v_26)) (or ?v_25 ?v_27)) (or ?v_26 ?v_27)) (or ?v_28 ?v_29)) (or ?v_28 ?v_30)) (or ?v_28 ?v_31)) (or ?v_29 ?v_30)) (or ?v_29 ?v_31)) (or ?v_30 ?v_31)) (or ?v_32 ?v_33)) (or ?v_32 ?v_34)) (or ?v_32 ?v_35)) (or ?v_33 ?v_34)) (or ?v_33 ?v_35)) (or ?v_34 ?v_35)) (or ?v_36 ?v_37)) (or ?v_36 ?v_38)) (or ?v_36 ?v_39)) (or ?v_37 ?v_38)) (or ?v_37 ?v_39)) (or ?v_38 ?v_39)) (or ?v_40 ?v_41)) (or ?v_122 (not ?v_41))) (or ?v_42 ?v_43)) (or ?v_121 (not ?v_43))) (or ?v_44 ?v_45)) (or ?v_127 (not ?v_45))) (or ?v_46 ?v_47)) (or ?v_126 (not ?v_47))) (or ?v_48 ?v_49)) (or ?v_131 (not ?v_49))) (or ?v_50 ?v_51)) (or ?v_130 (not ?v_51))) (or ?v_52 ?v_53)) (or ?v_135 (not ?v_53))) (or ?v_54 ?v_55)) (or ?v_134 (not ?v_55))) (or ?v_56 ?v_57)) (or ?v_139 (not ?v_57))) (or ?v_58 ?v_59)) (or ?v_138 (not ?v_59))) (or ?v_1 ?v_62)) (or ?v_5 (<= ?v_153 10))) (or ?v_9 ?v_70)) (or ?v_13 (<= ?v_154 10))) (or ?v_17 ?v_77)) (or ?v_21 (<= ?v_155 10))) (or ?v_25 ?v_84)) (or ?v_29 (<= ?v_156 10))) (or ?v_33 ?v_91)) (or ?v_37 (<= ?v_157 10))) (or (or (or (or (or (or AT0_PROC1_WAIT AT0_DELTA) AT0_PROC1_SW_A_B_TAU) AT0_PROC1_SW_B_C_TAU) AT0_PROC1_SW_C_B_TAU) AT0_PROC1_SW_C_CS_TAU) AT0_PROC1_SW_CS_A_TAU)) (or (or (or (or (or (or AT0_PROC2_WAIT AT0_DELTA) AT0_PROC2_SW_A_B_TAU) AT0_PROC2_SW_B_C_TAU) AT0_PROC2_SW_C_B_TAU) AT0_PROC2_SW_C_CS_TAU) AT0_PROC2_SW_CS_A_TAU)) (or (or (or (or (or (or AT0_PROC3_WAIT AT0_DELTA) AT0_PROC3_SW_A_B_TAU) AT0_PROC3_SW_B_C_TAU) AT0_PROC3_SW_C_B_TAU) AT0_PROC3_SW_C_CS_TAU) AT0_PROC3_SW_CS_A_TAU)) (or (or (or (or (or (or AT0_PROC4_WAIT AT0_DELTA) AT0_PROC4_SW_A_B_TAU) AT0_PROC4_SW_B_C_TAU) AT0_PROC4_SW_C_B_TAU) AT0_PROC4_SW_C_CS_TAU) AT0_PROC4_SW_CS_A_TAU)) (or (or (or (or (or (or AT0_PROC5_WAIT AT0_DELTA) AT0_PROC5_SW_A_B_TAU) AT0_PROC5_SW_B_C_TAU) AT0_PROC5_SW_C_B_TAU) AT0_PROC5_SW_C_CS_TAU) AT0_PROC5_SW_CS_A_TAU)) (or ?v_60 AT0_PROC1_A)) (or ?v_60 AT0_PROC1_TAU)) (or ?v_60 AT1_PROC1_B)) (or ?v_60 ?v_42)) (or ?v_61 AT0_PROC1_B)) (or ?v_61 AT0_PROC1_TAU)) (or ?v_61 AT1_PROC1_C)) (or ?v_61 ?v_62)) (or ?v_61 ?v_42)) (or ?v_63 AT0_PROC1_C)) (or ?v_63 AT0_PROC1_TAU)) (or ?v_63 AT1_PROC1_B)) (or ?v_63 ?v_42)) (or ?v_64 AT0_PROC1_C)) (or ?v_64 AT0_PROC1_TAU)) (or ?v_64 AT1_PROC1_CS)) (or ?v_64 (> ?v_65 10))) (or ?v_64 ?v_97)) (or ?v_66 AT0_PROC1_CS)) (or ?v_66 AT0_PROC1_TAU)) (or ?v_66 AT1_PROC1_A)) (or ?v_66 ?v_42)) (or ?v_60 ?v_67)) (or ?v_61 ?v_67)) (or ?v_63 ?v_67)) (or ?v_64 ?v_67)) (or ?v_66 ?v_67)) (or ?v_68 AT0_PROC2_A)) (or ?v_68 AT0_PROC2_TAU)) (or ?v_68 AT1_PROC2_B)) (or ?v_68 ?v_46)) (or ?v_69 AT0_PROC2_B)) (or ?v_69 AT0_PROC2_TAU)) (or ?v_69 AT1_PROC2_C)) (or ?v_69 ?v_70)) (or ?v_69 ?v_46)) (or ?v_71 AT0_PROC2_C)) (or ?v_71 AT0_PROC2_TAU)) (or ?v_71 AT1_PROC2_B)) (or ?v_71 ?v_46)) (or ?v_72 AT0_PROC2_C)) (or ?v_72 AT0_PROC2_TAU)) (or ?v_72 AT1_PROC2_CS)) (or ?v_72 (> ?v_73 10))) (or ?v_72 ?v_99)) (or ?v_74 AT0_PROC2_CS)) (or ?v_74 AT0_PROC2_TAU)) (or ?v_74 AT1_PROC2_A)) (or ?v_74 ?v_46)) (or ?v_68 ?v_67)) (or ?v_69 ?v_67)) (or ?v_71 ?v_67)) (or ?v_72 ?v_67)) (or ?v_74 ?v_67)) (or ?v_75 AT0_PROC3_A)) (or ?v_75 AT0_PROC3_TAU)) (or ?v_75 AT1_PROC3_B)) (or ?v_75 ?v_50)) (or ?v_76 AT0_PROC3_B)) (or ?v_76 AT0_PROC3_TAU)) (or ?v_76 AT1_PROC3_C)) (or ?v_76 ?v_77)) (or ?v_76 ?v_50)) (or ?v_78 AT0_PROC3_C)) (or ?v_78 AT0_PROC3_TAU)) (or ?v_78 AT1_PROC3_B)) (or ?v_78 ?v_50)) (or ?v_79 AT0_PROC3_C)) (or ?v_79 AT0_PROC3_TAU)) (or ?v_79 AT1_PROC3_CS)) (or ?v_79 (> ?v_80 10))) (or ?v_79 ?v_101)) (or ?v_81 AT0_PROC3_CS)) (or ?v_81 AT0_PROC3_TAU)) (or ?v_81 AT1_PROC3_A)) (or ?v_81 ?v_50)) (or ?v_75 ?v_67)) (or ?v_76 ?v_67)) (or ?v_78 ?v_67)) (or ?v_79 ?v_67)) (or ?v_81 ?v_67)) (or ?v_82 AT0_PROC4_A)) (or ?v_82 AT0_PROC4_TAU)) (or ?v_82 AT1_PROC4_B)) (or ?v_82 ?v_54)) (or ?v_83 AT0_PROC4_B)) (or ?v_83 AT0_PROC4_TAU)) (or ?v_83 AT1_PROC4_C)) (or ?v_83 ?v_84)) (or ?v_83 ?v_54)) (or ?v_85 AT0_PROC4_C)) (or ?v_85 AT0_PROC4_TAU)) (or ?v_85 AT1_PROC4_B)) (or ?v_85 ?v_54)) (or ?v_86 AT0_PROC4_C)) (or ?v_86 AT0_PROC4_TAU)) (or ?v_86 AT1_PROC4_CS)) (or ?v_86 (> ?v_87 10))) (or ?v_86 ?v_103)) (or ?v_88 AT0_PROC4_CS)) (or ?v_88 AT0_PROC4_TAU)) (or ?v_88 AT1_PROC4_A)) (or ?v_88 ?v_54)) (or ?v_82 ?v_67)) (or ?v_83 ?v_67)) (or ?v_85 ?v_67)) (or ?v_86 ?v_67)) (or ?v_88 ?v_67)) (or ?v_89 AT0_PROC5_A)) (or ?v_89 AT0_PROC5_TAU)) (or ?v_89 AT1_PROC5_B)) (or ?v_89 ?v_58)) (or ?v_90 AT0_PROC5_B)) (or ?v_90 AT0_PROC5_TAU)) (or ?v_90 AT1_PROC5_C)) (or ?v_90 ?v_91)) (or ?v_90 ?v_58)) (or ?v_92 AT0_PROC5_C)) (or ?v_92 AT0_PROC5_TAU)) (or ?v_92 AT1_PROC5_B)) (or ?v_92 ?v_58)) (or ?v_93 AT0_PROC5_C)) (or ?v_93 AT0_PROC5_TAU)) (or ?v_93 AT1_PROC5_CS)) (or ?v_93 (> ?v_94 10))) (or ?v_93 ?v_105)) (or ?v_95 AT0_PROC5_CS)) (or ?v_95 AT0_PROC5_TAU)) (or ?v_95 AT1_PROC5_A)) (or ?v_95 ?v_58)) (or ?v_89 ?v_67)) (or ?v_90 ?v_67)) (or ?v_92 ?v_67)) (or ?v_93 ?v_67)) (or ?v_95 ?v_67)) (or (or ?v_96 ?v_0) AT1_PROC1_A)) (or (or ?v_96 AT0_PROC1_A) ?v_4)) (or (or ?v_96 ?v_1) AT1_PROC1_B)) (or (or ?v_96 AT0_PROC1_B) ?v_5)) (or (or ?v_96 ?v_2) AT1_PROC1_C)) (or (or ?v_96 AT0_PROC1_C) ?v_6)) (or (or ?v_96 ?v_3) AT1_PROC1_CS)) (or (or ?v_96 AT0_PROC1_CS) ?v_7)) (or ?v_96 ?v_107)) (or ?v_96 ?v_97)) (or ?v_96 ?v_67)) (or (or ?v_98 ?v_8) AT1_PROC2_A)) (or (or ?v_98 AT0_PROC2_A) ?v_12)) (or (or ?v_98 ?v_9) AT1_PROC2_B)) (or (or ?v_98 AT0_PROC2_B) ?v_13)) (or (or ?v_98 ?v_10) AT1_PROC2_C)) (or (or ?v_98 AT0_PROC2_C) ?v_14)) (or (or ?v_98 ?v_11) AT1_PROC2_CS)) (or (or ?v_98 AT0_PROC2_CS) ?v_15)) (or ?v_98 ?v_108)) (or ?v_98 ?v_99)) (or ?v_98 ?v_67)) (or (or ?v_100 ?v_16) AT1_PROC3_A)) (or (or ?v_100 AT0_PROC3_A) ?v_20)) (or (or ?v_100 ?v_17) AT1_PROC3_B)) (or (or ?v_100 AT0_PROC3_B) ?v_21)) (or (or ?v_100 ?v_18) AT1_PROC3_C)) (or (or ?v_100 AT0_PROC3_C) ?v_22)) (or (or ?v_100 ?v_19) AT1_PROC3_CS)) (or (or ?v_100 AT0_PROC3_CS) ?v_23)) (or ?v_100 ?v_110)) (or ?v_100 ?v_101)) (or ?v_100 ?v_67)) (or (or ?v_102 ?v_24) AT1_PROC4_A)) (or (or ?v_102 AT0_PROC4_A) ?v_28)) (or (or ?v_102 ?v_25) AT1_PROC4_B)) (or (or ?v_102 AT0_PROC4_B) ?v_29)) (or (or ?v_102 ?v_26) AT1_PROC4_C)) (or (or ?v_102 AT0_PROC4_C) ?v_30)) (or (or ?v_102 ?v_27) AT1_PROC4_CS)) (or (or ?v_102 AT0_PROC4_CS) ?v_31)) (or ?v_102 ?v_111)) (or ?v_102 ?v_103)) (or ?v_102 ?v_67)) (or (or ?v_104 ?v_32) AT1_PROC5_A)) (or (or ?v_104 AT0_PROC5_A) ?v_36)) (or (or ?v_104 ?v_33) AT1_PROC5_B)) (or (or ?v_104 AT0_PROC5_B) ?v_37)) (or (or ?v_104 ?v_34) AT1_PROC5_C)) (or (or ?v_104 AT0_PROC5_C) ?v_38)) (or (or ?v_104 ?v_35) AT1_PROC5_CS)) (or (or ?v_104 AT0_PROC5_CS) ?v_39)) (or ?v_104 ?v_112)) (or ?v_104 ?v_105)) (or ?v_104 ?v_67)) (or (or ?v_106 ?v_0) AT1_PROC1_A)) (or (or ?v_106 AT0_PROC1_A) ?v_4)) (or (or ?v_106 ?v_1) AT1_PROC1_B)) (or (or ?v_106 AT0_PROC1_B) ?v_5)) (or (or ?v_106 ?v_2) AT1_PROC1_C)) (or (or ?v_106 AT0_PROC1_C) ?v_6)) (or (or ?v_106 ?v_3) AT1_PROC1_CS)) (or (or ?v_106 AT0_PROC1_CS) ?v_7)) (or ?v_106 ?v_97)) (or ?v_106 ?v_107)) ?v_109) (or (or ?v_106 ?v_8) AT1_PROC2_A)) (or (or ?v_106 AT0_PROC2_A) ?v_12)) (or (or ?v_106 ?v_9) AT1_PROC2_B)) (or (or ?v_106 AT0_PROC2_B) ?v_13)) (or (or ?v_106 ?v_10) AT1_PROC2_C)) (or (or ?v_106 AT0_PROC2_C) ?v_14)) (or (or ?v_106 ?v_11) AT1_PROC2_CS)) (or (or ?v_106 AT0_PROC2_CS) ?v_15)) (or ?v_106 ?v_99)) (or ?v_106 ?v_108)) ?v_109) (or (or ?v_106 ?v_16) AT1_PROC3_A)) (or (or ?v_106 AT0_PROC3_A) ?v_20)) (or (or ?v_106 ?v_17) AT1_PROC3_B)) (or (or ?v_106 AT0_PROC3_B) ?v_21)) (or (or ?v_106 ?v_18) AT1_PROC3_C)) (or (or ?v_106 AT0_PROC3_C) ?v_22)) (or (or ?v_106 ?v_19) AT1_PROC3_CS)) (or (or ?v_106 AT0_PROC3_CS) ?v_23)) (or ?v_106 ?v_101)) (or ?v_106 ?v_110)) ?v_109) (or (or ?v_106 ?v_24) AT1_PROC4_A)) (or (or ?v_106 AT0_PROC4_A) ?v_28)) (or (or ?v_106 ?v_25) AT1_PROC4_B)) (or (or ?v_106 AT0_PROC4_B) ?v_29)) (or (or ?v_106 ?v_26) AT1_PROC4_C)) (or (or ?v_106 AT0_PROC4_C) ?v_30)) (or (or ?v_106 ?v_27) AT1_PROC4_CS)) (or (or ?v_106 AT0_PROC4_CS) ?v_31)) (or ?v_106 ?v_103)) (or ?v_106 ?v_111)) ?v_109) (or (or ?v_106 ?v_32) AT1_PROC5_A)) (or (or ?v_106 AT0_PROC5_A) ?v_36)) (or (or ?v_106 ?v_33) AT1_PROC5_B)) (or (or ?v_106 AT0_PROC5_B) ?v_37)) (or (or ?v_106 ?v_34) AT1_PROC5_C)) (or (or ?v_106 AT0_PROC5_C) ?v_38)) (or (or ?v_106 ?v_35) AT1_PROC5_CS)) (or (or ?v_106 AT0_PROC5_CS) ?v_39)) (or ?v_106 ?v_105)) (or ?v_106 ?v_112)) ?v_109) (or ?v_97 ?v_113)) (or ?v_119 (not ?v_113))) (or ?v_99 ?v_114)) (or ?v_125 (not ?v_114))) (or ?v_101 ?v_115)) (or ?v_129 (not ?v_115))) (or ?v_103 ?v_116)) (or ?v_133 (not ?v_116))) (or ?v_105 ?v_117)) (or ?v_137 (not ?v_117))) (or ?v_67 ?v_118)) (or ?v_120 ?v_124)) (or (or (or ?v_40 ?v_119) ?v_120) ?v_121)) (or (or (or ?v_122 ?v_97) ?v_120) ?v_121)) (or (or ?v_123 ?v_67) ?v_121)) (or (or ?v_123 ?v_120) ?v_42)) (or (or (or (not (< AT0_Z AT0_PROC1_X)) ?v_119) ?v_124) (< AT1_Z AT1_PROC1_X))) (or (or (or ?v_44 ?v_125) ?v_120) ?v_126)) (or (or (or ?v_127 ?v_99) ?v_120) ?v_126)) (or (or ?v_128 ?v_67) ?v_126)) (or (or ?v_128 ?v_120) ?v_46)) (or (or (or (not (< AT0_Z AT0_PROC2_X)) ?v_125) ?v_124) (< AT1_Z AT1_PROC2_X))) (or (or (or ?v_48 ?v_129) ?v_120) ?v_130)) (or (or (or ?v_131 ?v_101) ?v_120) ?v_130)) (or (or ?v_132 ?v_67) ?v_130)) (or (or ?v_132 ?v_120) ?v_50)) (or (or (or (not (< AT0_Z AT0_PROC3_X)) ?v_129) ?v_124) (< AT1_Z AT1_PROC3_X))) (or (or (or ?v_52 ?v_133) ?v_120) ?v_134)) (or (or (or ?v_135 ?v_103) ?v_120) ?v_134)) (or (or ?v_136 ?v_67) ?v_134)) (or (or ?v_136 ?v_120) ?v_54)) (or (or (or (not (< AT0_Z AT0_PROC4_X)) ?v_133) ?v_124) (< AT1_Z AT1_PROC4_X))) (or (or (or ?v_56 ?v_137) ?v_120) ?v_138)) (or (or (or ?v_139 ?v_105) ?v_120) ?v_138)) (or (or ?v_140 ?v_67) ?v_138)) (or (or ?v_140 ?v_120) ?v_58)) (or (or (or (not (< AT0_Z AT0_PROC5_X)) ?v_137) ?v_124) (< AT1_Z AT1_PROC5_X))) AT0_PROC1_A) AT0_PROC2_A) AT0_PROC3_A) AT0_PROC4_A) AT0_PROC5_A) ?v_40) ?v_44) ?v_48) ?v_52) ?v_56) AT0_ID0) (or (or (or (or ?v_96 ?v_98) ?v_100) ?v_102) ?v_104)) (or ?v_141 ?v_142)) (or ?v_141 ?v_143)) (or ?v_141 ?v_144)) (or ?v_141 ?v_145)) (or ?v_141 ?v_146)) (or ?v_142 ?v_143)) (or ?v_142 ?v_144)) (or ?v_142 ?v_145)) (or ?v_142 ?v_146)) (or ?v_143 ?v_144)) (or ?v_143 ?v_145)) (or ?v_143 ?v_146)) (or ?v_144 ?v_145)) (or ?v_144 ?v_146)) (or ?v_145 ?v_146)) (or ?v_147 ?v_148)) (or ?v_147 ?v_149)) (or ?v_147 ?v_150)) (or ?v_147 ?v_151)) (or ?v_147 ?v_152)) (or ?v_148 ?v_149)) (or ?v_148 ?v_150)) (or ?v_148 ?v_151)) (or ?v_148 ?v_152)) (or ?v_149 ?v_150)) (or ?v_149 ?v_151)) (or ?v_149 ?v_152)) (or ?v_150 ?v_151)) (or ?v_150 ?v_152)) (or ?v_151 ?v_152)) (or ?v_60 AT0_ID0)) (or ?v_60 AT1_ID0)) (or ?v_61 AT1_ID1)) (or ?v_63 AT0_ID0)) (or ?v_63 AT1_ID0)) (or ?v_64 AT0_ID1)) (or ?v_64 AT1_ID1)) (or ?v_66 AT1_ID0)) (or (or ?v_106 ?v_142) AT1_ID1)) (or ?v_68 AT0_ID0)) (or ?v_68 AT1_ID0)) (or ?v_69 AT1_ID2)) (or ?v_71 AT0_ID0)) (or ?v_71 AT1_ID0)) (or ?v_72 AT0_ID2)) (or ?v_72 AT1_ID2)) (or ?v_74 AT1_ID0)) (or (or ?v_106 ?v_143) AT1_ID2)) (or ?v_75 AT0_ID0)) (or ?v_75 AT1_ID0)) (or ?v_76 AT1_ID3)) (or ?v_78 AT0_ID0)) (or ?v_78 AT1_ID0)) (or ?v_79 AT0_ID3)) (or ?v_79 AT1_ID3)) (or ?v_81 AT1_ID0)) (or (or ?v_106 ?v_144) AT1_ID3)) (or ?v_82 AT0_ID0)) (or ?v_82 AT1_ID0)) (or ?v_83 AT1_ID4)) (or ?v_85 AT0_ID0)) (or ?v_85 AT1_ID0)) (or ?v_86 AT0_ID4)) (or ?v_86 AT1_ID4)) (or ?v_88 AT1_ID0)) (or (or ?v_106 ?v_145) AT1_ID4)) (or ?v_89 AT0_ID0)) (or ?v_89 AT1_ID0)) (or ?v_90 AT1_ID5)) (or ?v_92 AT0_ID0)) (or ?v_92 AT1_ID0)) (or ?v_93 AT0_ID5)) (or ?v_93 AT1_ID5)) (or ?v_95 AT1_ID0)) (or (or ?v_106 ?v_146) AT1_ID5)) (or (or ?v_106 ?v_141) AT1_ID0)) (or ?v_4 AT1_PROC1_A)) (or AT1_PROC1_A ?v_4)) (or ?v_5 AT1_PROC1_B)) (or AT1_PROC1_B ?v_5)) (or ?v_6 AT1_PROC1_C)) (or AT1_PROC1_C ?v_6)) (or ?v_7 AT1_PROC1_CS)) (or AT1_PROC1_CS ?v_7)) (or ?v_148 AT1_ID1)) (or AT1_ID1 ?v_148)) (= ?v_153 ?v_153)) (or ?v_12 AT1_PROC2_A)) (or AT1_PROC2_A ?v_12)) (or ?v_13 AT1_PROC2_B)) (or AT1_PROC2_B ?v_13)) (or ?v_14 AT1_PROC2_C)) (or AT1_PROC2_C ?v_14)) (or ?v_15 AT1_PROC2_CS)) (or AT1_PROC2_CS ?v_15)) (or ?v_149 AT1_ID2)) (or AT1_ID2 ?v_149)) (= ?v_154 ?v_154)) (or ?v_20 AT1_PROC3_A)) (or AT1_PROC3_A ?v_20)) (or ?v_21 AT1_PROC3_B)) (or AT1_PROC3_B ?v_21)) (or ?v_22 AT1_PROC3_C)) (or AT1_PROC3_C ?v_22)) (or ?v_23 AT1_PROC3_CS)) (or AT1_PROC3_CS ?v_23)) (or ?v_150 AT1_ID3)) (or AT1_ID3 ?v_150)) (= ?v_155 ?v_155)) (or ?v_28 AT1_PROC4_A)) (or AT1_PROC4_A ?v_28)) (or ?v_29 AT1_PROC4_B)) (or AT1_PROC4_B ?v_29)) (or ?v_30 AT1_PROC4_C)) (or AT1_PROC4_C ?v_30)) (or ?v_31 AT1_PROC4_CS)) (or AT1_PROC4_CS ?v_31)) (or ?v_151 AT1_ID4)) (or AT1_ID4 ?v_151)) (= ?v_156 ?v_156)) (or ?v_36 AT1_PROC5_A)) (or AT1_PROC5_A ?v_36)) (or ?v_37 AT1_PROC5_B)) (or AT1_PROC5_B ?v_37)) (or ?v_38 AT1_PROC5_C)) (or AT1_PROC5_C ?v_38)) (or ?v_39 AT1_PROC5_CS)) (or AT1_PROC5_CS ?v_39)) (or ?v_152 AT1_ID5)) (or AT1_ID5 ?v_152)) (= ?v_157 ?v_157)) AT1_PROC1_B) ?v_7))))))))))))))))))))
(check-sat)
(exit)