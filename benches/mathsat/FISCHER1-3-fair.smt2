(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
Older mathsat benchmarks.  Contact Mathsat group at http://mathsat.itc.it/ for
more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun AT2_PROC1_X () Int)
(declare-fun AT0_PROC1_X () Int)
(declare-fun AT1_PROC1_SW_B_C_TAU () Bool)
(declare-fun AT0_ID0 () Bool)
(declare-fun AT0_ID1 () Bool)
(declare-fun AT2_PROC1_SW_B_C_TAU () Bool)
(declare-fun AT1_PROC1_WAIT () Bool)
(declare-fun AT2_Z () Int)
(declare-fun AT2_PROC1_C () Bool)
(declare-fun AT2_PROC1_B () Bool)
(declare-fun AT2_PROC1_A () Bool)
(declare-fun AT0_PROC1_C () Bool)
(declare-fun AT0_PROC1_B () Bool)
(declare-fun AT0_PROC1_A () Bool)
(declare-fun AT2_PROC1_CS () Bool)
(declare-fun AT1_ID0 () Bool)
(declare-fun AT1_ID1 () Bool)
(declare-fun AT0_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT3_PROC1_X () Int)
(declare-fun AT1_PROC1_X () Int)
(declare-fun AT1_Z () Int)
(declare-fun AT2_ID0 () Bool)
(declare-fun AT2_ID1 () Bool)
(declare-fun AT0_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT0_PROC1_CS () Bool)
(declare-fun AT0_PROC1_TAU () Bool)
(declare-fun AT2_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT0_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT0_PROC1_WAIT () Bool)
(declare-fun AT3_PROC1_CS () Bool)
(declare-fun AT1_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT3_PROC1_C () Bool)
(declare-fun AT3_PROC1_B () Bool)
(declare-fun AT3_PROC1_A () Bool)
(declare-fun AT1_PROC1_C () Bool)
(declare-fun AT1_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT1_PROC1_B () Bool)
(declare-fun AT1_PROC1_A () Bool)
(declare-fun AT2_PROC1_SW_C_B_TAU () Bool)
(declare-fun AT0_DELTA () Bool)
(declare-fun AT1_PROC1_TAU () Bool)
(declare-fun AT1_PROC1_CS () Bool)
(declare-fun AT3_Z () Int)
(declare-fun AT3_ID0 () Bool)
(declare-fun AT0_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT3_ID1 () Bool)
(declare-fun AT1_DELTA () Bool)
(declare-fun AT2_PROC1_TAU () Bool)
(declare-fun AT2_PROC1_SW_C_CS_TAU () Bool)
(declare-fun AT1_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT0_Z () Int)
(declare-fun AT2_PROC1_WAIT () Bool)
(declare-fun AT1_PROC1_SW_CS_A_TAU () Bool)
(declare-fun AT2_PROC1_SW_A_B_TAU () Bool)
(declare-fun AT2_DELTA () Bool)
(declare-fun AT0_PROC1_SW_B_C_TAU () Bool)
(assert (let ((?v_0 (not AT0_PROC1_A)) (?v_1 (not AT0_PROC1_B)) (?v_2 (not AT0_PROC1_C)) (?v_3 (not AT0_PROC1_CS)) (?v_4 (not AT1_PROC1_A)) (?v_5 (not AT1_PROC1_B)) (?v_6 (not AT1_PROC1_C)) (?v_7 (not AT1_PROC1_CS)) (?v_8 (not AT2_PROC1_A)) (?v_9 (not AT2_PROC1_B)) (?v_10 (not AT2_PROC1_C)) (?v_11 (not AT2_PROC1_CS)) (?v_12 (not AT3_PROC1_A)) (?v_13 (not AT3_PROC1_B)) (?v_14 (not AT3_PROC1_C)) (?v_15 (not AT3_PROC1_CS)) (?v_16 (= AT0_PROC1_X AT0_Z)) (?v_17 (> AT0_PROC1_X AT0_Z))) (let ((?v_69 (not ?v_16)) (?v_18 (= AT1_PROC1_X AT1_Z)) (?v_19 (> AT1_PROC1_X AT1_Z))) (let ((?v_68 (not ?v_18)) (?v_20 (= AT2_PROC1_X AT2_Z)) (?v_21 (> AT2_PROC1_X AT2_Z))) (let ((?v_74 (not ?v_20)) (?v_22 (= AT3_PROC1_X AT3_Z)) (?v_23 (> AT3_PROC1_X AT3_Z))) (let ((?v_80 (not ?v_22)) (?v_29 (- AT0_PROC1_X AT0_Z))) (let ((?v_26 (<= ?v_29 10)) (?v_36 (- AT1_PROC1_X AT1_Z))) (let ((?v_33 (<= ?v_36 10)) (?v_43 (- AT2_PROC1_X AT2_Z))) (let ((?v_40 (<= ?v_43 10)) (?v_24 (not AT0_PROC1_SW_A_B_TAU)) (?v_25 (not AT0_PROC1_SW_B_C_TAU)) (?v_27 (not AT0_PROC1_SW_C_B_TAU)) (?v_28 (not AT0_PROC1_SW_C_CS_TAU)) (?v_49 (= AT1_PROC1_X AT0_PROC1_X)) (?v_30 (not AT0_PROC1_SW_CS_A_TAU)) (?v_31 (not AT1_PROC1_SW_A_B_TAU)) (?v_32 (not AT1_PROC1_SW_B_C_TAU)) (?v_34 (not AT1_PROC1_SW_C_B_TAU)) (?v_35 (not AT1_PROC1_SW_C_CS_TAU)) (?v_51 (= AT2_PROC1_X AT1_PROC1_X)) (?v_37 (not AT1_PROC1_SW_CS_A_TAU)) (?v_38 (not AT2_PROC1_SW_A_B_TAU)) (?v_39 (not AT2_PROC1_SW_B_C_TAU)) (?v_41 (not AT2_PROC1_SW_C_B_TAU)) (?v_42 (not AT2_PROC1_SW_C_CS_TAU)) (?v_53 (= AT3_PROC1_X AT2_PROC1_X)) (?v_44 (not AT2_PROC1_SW_CS_A_TAU)) (?v_45 (= AT1_Z AT0_Z)) (?v_46 (= AT2_Z AT1_Z)) (?v_47 (= AT3_Z AT2_Z)) (?v_48 (not AT0_PROC1_WAIT)) (?v_55 (not AT0_PROC1_TAU)) (?v_50 (not AT1_PROC1_WAIT)) (?v_57 (not AT1_PROC1_TAU)) (?v_52 (not AT2_PROC1_WAIT)) (?v_59 (not AT2_PROC1_TAU)) (?v_54 (not AT0_DELTA)) (?v_63 (< AT1_Z AT0_Z)) (?v_56 (not AT1_DELTA)) (?v_64 (< AT2_Z AT1_Z)) (?v_58 (not AT2_DELTA)) (?v_65 (< AT3_Z AT2_Z)) (?v_60 (< AT1_PROC1_X AT0_PROC1_X))) (let ((?v_66 (not ?v_49)) (?v_61 (< AT2_PROC1_X AT1_PROC1_X)) (?v_72 (not ?v_51)) (?v_62 (< AT3_PROC1_X AT2_PROC1_X)) (?v_78 (not ?v_53)) (?v_67 (not ?v_45)) (?v_71 (not ?v_63)) (?v_73 (not ?v_46)) (?v_77 (not ?v_64)) (?v_79 (not ?v_47)) (?v_83 (not ?v_65))) (let ((?v_70 (or ?v_69 ?v_66)) (?v_76 (< AT1_Z AT1_PROC1_X)) (?v_75 (or ?v_68 ?v_72)) (?v_82 (< AT2_Z AT2_PROC1_X)) (?v_81 (or ?v_74 ?v_78)) (?v_85 (not AT0_ID0)) (?v_84 (not AT0_ID1)) (?v_87 (not AT1_ID0)) (?v_86 (not AT1_ID1)) (?v_89 (not AT2_ID0)) (?v_88 (not AT2_ID1)) (?v_90 (not AT3_ID1)) (?v_91 (- AT3_PROC1_X AT3_Z))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_0 ?v_1) (or ?v_0 ?v_2)) (or ?v_0 ?v_3)) (or ?v_1 ?v_2)) (or ?v_1 ?v_3)) (or ?v_2 ?v_3)) (or ?v_4 ?v_5)) (or ?v_4 ?v_6)) (or ?v_4 ?v_7)) (or ?v_5 ?v_6)) (or ?v_5 ?v_7)) (or ?v_6 ?v_7)) (or ?v_8 ?v_9)) (or ?v_8 ?v_10)) (or ?v_8 ?v_11)) (or ?v_9 ?v_10)) (or ?v_9 ?v_11)) (or ?v_10 ?v_11)) (or ?v_12 ?v_13)) (or ?v_12 ?v_14)) (or ?v_12 ?v_15)) (or ?v_13 ?v_14)) (or ?v_13 ?v_15)) (or ?v_14 ?v_15)) (or ?v_16 ?v_17)) (or ?v_69 (not ?v_17))) (or ?v_18 ?v_19)) (or ?v_68 (not ?v_19))) (or ?v_20 ?v_21)) (or ?v_74 (not ?v_21))) (or ?v_22 ?v_23)) (or ?v_80 (not ?v_23))) (or ?v_1 ?v_26)) (or ?v_5 ?v_33)) (or ?v_9 ?v_40)) (or ?v_13 (<= ?v_91 10))) (or (or (or (or (or (or AT0_PROC1_WAIT AT0_DELTA) AT0_PROC1_SW_A_B_TAU) AT0_PROC1_SW_B_C_TAU) AT0_PROC1_SW_C_B_TAU) AT0_PROC1_SW_C_CS_TAU) AT0_PROC1_SW_CS_A_TAU)) (or (or (or (or (or (or AT1_PROC1_WAIT AT1_DELTA) AT1_PROC1_SW_A_B_TAU) AT1_PROC1_SW_B_C_TAU) AT1_PROC1_SW_C_B_TAU) AT1_PROC1_SW_C_CS_TAU) AT1_PROC1_SW_CS_A_TAU)) (or (or (or (or (or (or AT2_PROC1_WAIT AT2_DELTA) AT2_PROC1_SW_A_B_TAU) AT2_PROC1_SW_B_C_TAU) AT2_PROC1_SW_C_B_TAU) AT2_PROC1_SW_C_CS_TAU) AT2_PROC1_SW_CS_A_TAU)) (or ?v_24 AT0_PROC1_A)) (or ?v_24 AT0_PROC1_TAU)) (or ?v_24 AT1_PROC1_B)) (or ?v_24 ?v_18)) (or ?v_25 AT0_PROC1_B)) (or ?v_25 AT0_PROC1_TAU)) (or ?v_25 AT1_PROC1_C)) (or ?v_25 ?v_26)) (or ?v_25 ?v_18)) (or ?v_27 AT0_PROC1_C)) (or ?v_27 AT0_PROC1_TAU)) (or ?v_27 AT1_PROC1_B)) (or ?v_27 ?v_18)) (or ?v_28 AT0_PROC1_C)) (or ?v_28 AT0_PROC1_TAU)) (or ?v_28 AT1_PROC1_CS)) (or ?v_28 (> ?v_29 10))) (or ?v_28 ?v_49)) (or ?v_30 AT0_PROC1_CS)) (or ?v_30 AT0_PROC1_TAU)) (or ?v_30 AT1_PROC1_A)) (or ?v_30 ?v_18)) (or ?v_31 AT1_PROC1_A)) (or ?v_31 AT1_PROC1_TAU)) (or ?v_31 AT2_PROC1_B)) (or ?v_31 ?v_20)) (or ?v_32 AT1_PROC1_B)) (or ?v_32 AT1_PROC1_TAU)) (or ?v_32 AT2_PROC1_C)) (or ?v_32 ?v_33)) (or ?v_32 ?v_20)) (or ?v_34 AT1_PROC1_C)) (or ?v_34 AT1_PROC1_TAU)) (or ?v_34 AT2_PROC1_B)) (or ?v_34 ?v_20)) (or ?v_35 AT1_PROC1_C)) (or ?v_35 AT1_PROC1_TAU)) (or ?v_35 AT2_PROC1_CS)) (or ?v_35 (> ?v_36 10))) (or ?v_35 ?v_51)) (or ?v_37 AT1_PROC1_CS)) (or ?v_37 AT1_PROC1_TAU)) (or ?v_37 AT2_PROC1_A)) (or ?v_37 ?v_20)) (or ?v_38 AT2_PROC1_A)) (or ?v_38 AT2_PROC1_TAU)) (or ?v_38 AT3_PROC1_B)) (or ?v_38 ?v_22)) (or ?v_39 AT2_PROC1_B)) (or ?v_39 AT2_PROC1_TAU)) (or ?v_39 AT3_PROC1_C)) (or ?v_39 ?v_40)) (or ?v_39 ?v_22)) (or ?v_41 AT2_PROC1_C)) (or ?v_41 AT2_PROC1_TAU)) (or ?v_41 AT3_PROC1_B)) (or ?v_41 ?v_22)) (or ?v_42 AT2_PROC1_C)) (or ?v_42 AT2_PROC1_TAU)) (or ?v_42 AT3_PROC1_CS)) (or ?v_42 (> ?v_43 10))) (or ?v_42 ?v_53)) (or ?v_44 AT2_PROC1_CS)) (or ?v_44 AT2_PROC1_TAU)) (or ?v_44 AT3_PROC1_A)) (or ?v_44 ?v_22)) (or ?v_24 ?v_45)) (or ?v_25 ?v_45)) (or ?v_27 ?v_45)) (or ?v_28 ?v_45)) (or ?v_30 ?v_45)) (or ?v_31 ?v_46)) (or ?v_32 ?v_46)) (or ?v_34 ?v_46)) (or ?v_35 ?v_46)) (or ?v_37 ?v_46)) (or ?v_38 ?v_47)) (or ?v_39 ?v_47)) (or ?v_41 ?v_47)) (or ?v_42 ?v_47)) (or ?v_44 ?v_47)) (or (or ?v_48 ?v_0) AT1_PROC1_A)) (or (or ?v_48 AT0_PROC1_A) ?v_4)) (or (or ?v_48 ?v_1) AT1_PROC1_B)) (or (or ?v_48 AT0_PROC1_B) ?v_5)) (or (or ?v_48 ?v_2) AT1_PROC1_C)) (or (or ?v_48 AT0_PROC1_C) ?v_6)) (or (or ?v_48 ?v_3) AT1_PROC1_CS)) (or (or ?v_48 AT0_PROC1_CS) ?v_7)) (or ?v_48 ?v_55)) (or ?v_48 ?v_49)) (or ?v_48 ?v_45)) (or (or ?v_50 ?v_4) AT2_PROC1_A)) (or (or ?v_50 AT1_PROC1_A) ?v_8)) (or (or ?v_50 ?v_5) AT2_PROC1_B)) (or (or ?v_50 AT1_PROC1_B) ?v_9)) (or (or ?v_50 ?v_6) AT2_PROC1_C)) (or (or ?v_50 AT1_PROC1_C) ?v_10)) (or (or ?v_50 ?v_7) AT2_PROC1_CS)) (or (or ?v_50 AT1_PROC1_CS) ?v_11)) (or ?v_50 ?v_57)) (or ?v_50 ?v_51)) (or ?v_50 ?v_46)) (or (or ?v_52 ?v_8) AT3_PROC1_A)) (or (or ?v_52 AT2_PROC1_A) ?v_12)) (or (or ?v_52 ?v_9) AT3_PROC1_B)) (or (or ?v_52 AT2_PROC1_B) ?v_13)) (or (or ?v_52 ?v_10) AT3_PROC1_C)) (or (or ?v_52 AT2_PROC1_C) ?v_14)) (or (or ?v_52 ?v_11) AT3_PROC1_CS)) (or (or ?v_52 AT2_PROC1_CS) ?v_15)) (or ?v_52 ?v_59)) (or ?v_52 ?v_53)) (or ?v_52 ?v_47)) (or (or ?v_54 ?v_0) AT1_PROC1_A)) (or (or ?v_54 AT0_PROC1_A) ?v_4)) (or (or ?v_54 ?v_1) AT1_PROC1_B)) (or (or ?v_54 AT0_PROC1_B) ?v_5)) (or (or ?v_54 ?v_2) AT1_PROC1_C)) (or (or ?v_54 AT0_PROC1_C) ?v_6)) (or (or ?v_54 ?v_3) AT1_PROC1_CS)) (or (or ?v_54 AT0_PROC1_CS) ?v_7)) (or ?v_54 ?v_49)) (or ?v_54 ?v_55)) (or ?v_54 ?v_63)) (or (or ?v_56 ?v_4) AT2_PROC1_A)) (or (or ?v_56 AT1_PROC1_A) ?v_8)) (or (or ?v_56 ?v_5) AT2_PROC1_B)) (or (or ?v_56 AT1_PROC1_B) ?v_9)) (or (or ?v_56 ?v_6) AT2_PROC1_C)) (or (or ?v_56 AT1_PROC1_C) ?v_10)) (or (or ?v_56 ?v_7) AT2_PROC1_CS)) (or (or ?v_56 AT1_PROC1_CS) ?v_11)) (or ?v_56 ?v_51)) (or ?v_56 ?v_57)) (or ?v_56 ?v_64)) (or (or ?v_58 ?v_8) AT3_PROC1_A)) (or (or ?v_58 AT2_PROC1_A) ?v_12)) (or (or ?v_58 ?v_9) AT3_PROC1_B)) (or (or ?v_58 AT2_PROC1_B) ?v_13)) (or (or ?v_58 ?v_10) AT3_PROC1_C)) (or (or ?v_58 AT2_PROC1_C) ?v_14)) (or (or ?v_58 ?v_11) AT3_PROC1_CS)) (or (or ?v_58 AT2_PROC1_CS) ?v_15)) (or ?v_58 ?v_53)) (or ?v_58 ?v_59)) (or ?v_58 ?v_65)) (or ?v_49 ?v_60)) (or ?v_66 (not ?v_60))) (or ?v_51 ?v_61)) (or ?v_72 (not ?v_61))) (or ?v_53 ?v_62)) (or ?v_78 (not ?v_62))) (or ?v_54 ?v_56)) (or ?v_56 ?v_58)) (or ?v_45 ?v_63)) (or ?v_67 ?v_71)) (or ?v_46 ?v_64)) (or ?v_73 ?v_77)) (or ?v_47 ?v_65)) (or ?v_79 ?v_83)) (or (or (or ?v_16 ?v_66) ?v_67) ?v_68)) (or (or (or ?v_69 ?v_49) ?v_67) ?v_68)) (or (or ?v_70 ?v_45) ?v_68)) (or (or ?v_70 ?v_67) ?v_18)) (or (or (or (not (< AT0_Z AT0_PROC1_X)) ?v_66) ?v_71) ?v_76)) (or (or (or ?v_18 ?v_72) ?v_73) ?v_74)) (or (or (or ?v_68 ?v_51) ?v_73) ?v_74)) (or (or ?v_75 ?v_46) ?v_74)) (or (or ?v_75 ?v_73) ?v_20)) (or (or (or (not ?v_76) ?v_72) ?v_77) ?v_82)) (or (or (or ?v_20 ?v_78) ?v_79) ?v_80)) (or (or (or ?v_74 ?v_53) ?v_79) ?v_80)) (or (or ?v_81 ?v_47) ?v_80)) (or (or ?v_81 ?v_79) ?v_22)) (or (or (or (not ?v_82) ?v_78) ?v_83) (< AT3_Z AT3_PROC1_X))) AT0_PROC1_A) ?v_16) AT0_ID0) ?v_48) ?v_50) ?v_52) (or ?v_85 ?v_84)) (or ?v_87 ?v_86)) (or ?v_89 ?v_88)) (or (not AT3_ID0) ?v_90)) (or ?v_24 AT0_ID0)) (or ?v_24 AT1_ID0)) (or ?v_25 AT1_ID1)) (or ?v_27 AT0_ID0)) (or ?v_27 AT1_ID0)) (or ?v_28 AT0_ID1)) (or ?v_28 AT1_ID1)) (or ?v_30 AT1_ID0)) (or (or ?v_54 ?v_84) AT1_ID1)) (or (or ?v_54 ?v_85) AT1_ID0)) (or ?v_31 AT1_ID0)) (or ?v_31 AT2_ID0)) (or ?v_32 AT2_ID1)) (or ?v_34 AT1_ID0)) (or ?v_34 AT2_ID0)) (or ?v_35 AT1_ID1)) (or ?v_35 AT2_ID1)) (or ?v_37 AT2_ID0)) (or (or ?v_56 ?v_86) AT2_ID1)) (or (or ?v_56 ?v_87) AT2_ID0)) (or ?v_38 AT2_ID0)) (or ?v_38 AT3_ID0)) (or ?v_39 AT3_ID1)) (or ?v_41 AT2_ID0)) (or ?v_41 AT3_ID0)) (or ?v_42 AT2_ID1)) (or ?v_42 AT3_ID1)) (or ?v_44 AT3_ID0)) (or (or ?v_58 ?v_88) AT3_ID1)) (or (or ?v_58 ?v_89) AT3_ID0)) (or ?v_4 AT3_PROC1_A)) (or AT1_PROC1_A ?v_12)) (or ?v_5 AT3_PROC1_B)) (or AT1_PROC1_B ?v_13)) (or ?v_6 AT3_PROC1_C)) (or AT1_PROC1_C ?v_14)) (or ?v_7 AT3_PROC1_CS)) (or AT1_PROC1_CS ?v_15)) (or ?v_86 AT3_ID1)) (or AT1_ID1 ?v_90)) (= ?v_36 ?v_91)) (or (or AT1_PROC1_B AT2_PROC1_B) AT3_PROC1_B)) ?v_7) ?v_11) ?v_15))))))))))))
(check-sat)
(exit)
