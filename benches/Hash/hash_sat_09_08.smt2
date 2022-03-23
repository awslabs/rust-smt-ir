(set-info :smt-lib-version 2.6)
(set-logic QF_UFLIA)
(set-info :source | MathSat group |)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun hash_1 (Int) Int)
(declare-fun hash_2 (Int) Int)
(declare-fun hash_3 (Int) Int)
(declare-fun hash_4 (Int) Int)
(declare-fun hash_5 (Int) Int)
(declare-fun hash_6 (Int) Int)
(declare-fun hash_7 (Int) Int)
(declare-fun hash_8 (Int) Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x9 () Int)
(assert (let ((?v_0 (hash_1 x1)) (?v_1 (hash_1 x2)) (?v_2 (hash_1 x3)) (?v_3 (hash_1 x4)) (?v_4 (hash_1 x5)) (?v_5 (hash_1 x6)) (?v_6 (hash_1 x7)) (?v_7 (hash_1 x8)) (?v_8 (hash_1 x9)) (?v_9 (hash_2 x1)) (?v_10 (hash_2 x2)) (?v_11 (hash_2 x3)) (?v_12 (hash_2 x4)) (?v_13 (hash_2 x5)) (?v_14 (hash_2 x6)) (?v_15 (hash_2 x7)) (?v_16 (hash_2 x8)) (?v_17 (hash_2 x9)) (?v_18 (hash_3 x1)) (?v_19 (hash_3 x2)) (?v_20 (hash_3 x3)) (?v_21 (hash_3 x4)) (?v_22 (hash_3 x5)) (?v_23 (hash_3 x6)) (?v_24 (hash_3 x7)) (?v_25 (hash_3 x8)) (?v_26 (hash_3 x9)) (?v_27 (hash_4 x1)) (?v_28 (hash_4 x2)) (?v_29 (hash_4 x3)) (?v_30 (hash_4 x4)) (?v_31 (hash_4 x5)) (?v_32 (hash_4 x6)) (?v_33 (hash_4 x7)) (?v_34 (hash_4 x8)) (?v_35 (hash_4 x9)) (?v_36 (hash_5 x1)) (?v_37 (hash_5 x2)) (?v_38 (hash_5 x3)) (?v_39 (hash_5 x4)) (?v_40 (hash_5 x5)) (?v_41 (hash_5 x6)) (?v_42 (hash_5 x7)) (?v_43 (hash_5 x8)) (?v_44 (hash_5 x9)) (?v_45 (hash_6 x1)) (?v_46 (hash_6 x2)) (?v_47 (hash_6 x3)) (?v_48 (hash_6 x4)) (?v_49 (hash_6 x5)) (?v_50 (hash_6 x6)) (?v_51 (hash_6 x7)) (?v_52 (hash_6 x8)) (?v_53 (hash_6 x9)) (?v_54 (hash_7 x1)) (?v_55 (hash_7 x2)) (?v_56 (hash_7 x3)) (?v_57 (hash_7 x4)) (?v_58 (hash_7 x5)) (?v_59 (hash_7 x6)) (?v_60 (hash_7 x7)) (?v_61 (hash_7 x8)) (?v_62 (hash_7 x9)) (?v_63 (hash_8 x1)) (?v_64 (hash_8 x2)) (?v_65 (hash_8 x3)) (?v_66 (hash_8 x4)) (?v_67 (hash_8 x5)) (?v_68 (hash_8 x6)) (?v_69 (hash_8 x7)) (?v_70 (hash_8 x8)) (?v_71 (hash_8 x9)) (?v_72 (+ x1 x9)) (?v_73 (+ x1 x2))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (distinct ?v_0 ?v_1) (distinct ?v_0 ?v_2)) (distinct ?v_0 ?v_3)) (distinct ?v_0 ?v_4)) (distinct ?v_0 ?v_5)) (distinct ?v_0 ?v_6)) (distinct ?v_0 ?v_7)) (distinct ?v_0 ?v_8)) (distinct ?v_1 ?v_2)) (distinct ?v_1 ?v_3)) (distinct ?v_1 ?v_4)) (distinct ?v_1 ?v_5)) (distinct ?v_1 ?v_6)) (distinct ?v_1 ?v_7)) (distinct ?v_1 ?v_8)) (distinct ?v_2 ?v_3)) (distinct ?v_2 ?v_4)) (distinct ?v_2 ?v_5)) (distinct ?v_2 ?v_6)) (distinct ?v_2 ?v_7)) (distinct ?v_2 ?v_8)) (distinct ?v_3 ?v_4)) (distinct ?v_3 ?v_5)) (distinct ?v_3 ?v_6)) (distinct ?v_3 ?v_7)) (distinct ?v_3 ?v_8)) (distinct ?v_4 ?v_5)) (distinct ?v_4 ?v_6)) (distinct ?v_4 ?v_7)) (distinct ?v_4 ?v_8)) (distinct ?v_5 ?v_6)) (distinct ?v_5 ?v_7)) (distinct ?v_5 ?v_8)) (distinct ?v_6 ?v_7)) (distinct ?v_6 ?v_8)) (distinct ?v_7 ?v_8)) (distinct ?v_9 ?v_10)) (distinct ?v_9 ?v_11)) (distinct ?v_9 ?v_12)) (distinct ?v_9 ?v_13)) (distinct ?v_9 ?v_14)) (distinct ?v_9 ?v_15)) (distinct ?v_9 ?v_16)) (distinct ?v_9 ?v_17)) (distinct ?v_10 ?v_11)) (distinct ?v_10 ?v_12)) (distinct ?v_10 ?v_13)) (distinct ?v_10 ?v_14)) (distinct ?v_10 ?v_15)) (distinct ?v_10 ?v_16)) (distinct ?v_10 ?v_17)) (distinct ?v_11 ?v_12)) (distinct ?v_11 ?v_13)) (distinct ?v_11 ?v_14)) (distinct ?v_11 ?v_15)) (distinct ?v_11 ?v_16)) (distinct ?v_11 ?v_17)) (distinct ?v_12 ?v_13)) (distinct ?v_12 ?v_14)) (distinct ?v_12 ?v_15)) (distinct ?v_12 ?v_16)) (distinct ?v_12 ?v_17)) (distinct ?v_13 ?v_14)) (distinct ?v_13 ?v_15)) (distinct ?v_13 ?v_16)) (distinct ?v_13 ?v_17)) (distinct ?v_14 ?v_15)) (distinct ?v_14 ?v_16)) (distinct ?v_14 ?v_17)) (distinct ?v_15 ?v_16)) (distinct ?v_15 ?v_17)) (distinct ?v_16 ?v_17)) (distinct ?v_18 ?v_19)) (distinct ?v_18 ?v_20)) (distinct ?v_18 ?v_21)) (distinct ?v_18 ?v_22)) (distinct ?v_18 ?v_23)) (distinct ?v_18 ?v_24)) (distinct ?v_18 ?v_25)) (distinct ?v_18 ?v_26)) (distinct ?v_19 ?v_20)) (distinct ?v_19 ?v_21)) (distinct ?v_19 ?v_22)) (distinct ?v_19 ?v_23)) (distinct ?v_19 ?v_24)) (distinct ?v_19 ?v_25)) (distinct ?v_19 ?v_26)) (distinct ?v_20 ?v_21)) (distinct ?v_20 ?v_22)) (distinct ?v_20 ?v_23)) (distinct ?v_20 ?v_24)) (distinct ?v_20 ?v_25)) (distinct ?v_20 ?v_26)) (distinct ?v_21 ?v_22)) (distinct ?v_21 ?v_23)) (distinct ?v_21 ?v_24)) (distinct ?v_21 ?v_25)) (distinct ?v_21 ?v_26)) (distinct ?v_22 ?v_23)) (distinct ?v_22 ?v_24)) (distinct ?v_22 ?v_25)) (distinct ?v_22 ?v_26)) (distinct ?v_23 ?v_24)) (distinct ?v_23 ?v_25)) (distinct ?v_23 ?v_26)) (distinct ?v_24 ?v_25)) (distinct ?v_24 ?v_26)) (distinct ?v_25 ?v_26)) (distinct ?v_27 ?v_28)) (distinct ?v_27 ?v_29)) (distinct ?v_27 ?v_30)) (distinct ?v_27 ?v_31)) (distinct ?v_27 ?v_32)) (distinct ?v_27 ?v_33)) (distinct ?v_27 ?v_34)) (distinct ?v_27 ?v_35)) (distinct ?v_28 ?v_29)) (distinct ?v_28 ?v_30)) (distinct ?v_28 ?v_31)) (distinct ?v_28 ?v_32)) (distinct ?v_28 ?v_33)) (distinct ?v_28 ?v_34)) (distinct ?v_28 ?v_35)) (distinct ?v_29 ?v_30)) (distinct ?v_29 ?v_31)) (distinct ?v_29 ?v_32)) (distinct ?v_29 ?v_33)) (distinct ?v_29 ?v_34)) (distinct ?v_29 ?v_35)) (distinct ?v_30 ?v_31)) (distinct ?v_30 ?v_32)) (distinct ?v_30 ?v_33)) (distinct ?v_30 ?v_34)) (distinct ?v_30 ?v_35)) (distinct ?v_31 ?v_32)) (distinct ?v_31 ?v_33)) (distinct ?v_31 ?v_34)) (distinct ?v_31 ?v_35)) (distinct ?v_32 ?v_33)) (distinct ?v_32 ?v_34)) (distinct ?v_32 ?v_35)) (distinct ?v_33 ?v_34)) (distinct ?v_33 ?v_35)) (distinct ?v_34 ?v_35)) (distinct ?v_36 ?v_37)) (distinct ?v_36 ?v_38)) (distinct ?v_36 ?v_39)) (distinct ?v_36 ?v_40)) (distinct ?v_36 ?v_41)) (distinct ?v_36 ?v_42)) (distinct ?v_36 ?v_43)) (distinct ?v_36 ?v_44)) (distinct ?v_37 ?v_38)) (distinct ?v_37 ?v_39)) (distinct ?v_37 ?v_40)) (distinct ?v_37 ?v_41)) (distinct ?v_37 ?v_42)) (distinct ?v_37 ?v_43)) (distinct ?v_37 ?v_44)) (distinct ?v_38 ?v_39)) (distinct ?v_38 ?v_40)) (distinct ?v_38 ?v_41)) (distinct ?v_38 ?v_42)) (distinct ?v_38 ?v_43)) (distinct ?v_38 ?v_44)) (distinct ?v_39 ?v_40)) (distinct ?v_39 ?v_41)) (distinct ?v_39 ?v_42)) (distinct ?v_39 ?v_43)) (distinct ?v_39 ?v_44)) (distinct ?v_40 ?v_41)) (distinct ?v_40 ?v_42)) (distinct ?v_40 ?v_43)) (distinct ?v_40 ?v_44)) (distinct ?v_41 ?v_42)) (distinct ?v_41 ?v_43)) (distinct ?v_41 ?v_44)) (distinct ?v_42 ?v_43)) (distinct ?v_42 ?v_44)) (distinct ?v_43 ?v_44)) (distinct ?v_45 ?v_46)) (distinct ?v_45 ?v_47)) (distinct ?v_45 ?v_48)) (distinct ?v_45 ?v_49)) (distinct ?v_45 ?v_50)) (distinct ?v_45 ?v_51)) (distinct ?v_45 ?v_52)) (distinct ?v_45 ?v_53)) (distinct ?v_46 ?v_47)) (distinct ?v_46 ?v_48)) (distinct ?v_46 ?v_49)) (distinct ?v_46 ?v_50)) (distinct ?v_46 ?v_51)) (distinct ?v_46 ?v_52)) (distinct ?v_46 ?v_53)) (distinct ?v_47 ?v_48)) (distinct ?v_47 ?v_49)) (distinct ?v_47 ?v_50)) (distinct ?v_47 ?v_51)) (distinct ?v_47 ?v_52)) (distinct ?v_47 ?v_53)) (distinct ?v_48 ?v_49)) (distinct ?v_48 ?v_50)) (distinct ?v_48 ?v_51)) (distinct ?v_48 ?v_52)) (distinct ?v_48 ?v_53)) (distinct ?v_49 ?v_50)) (distinct ?v_49 ?v_51)) (distinct ?v_49 ?v_52)) (distinct ?v_49 ?v_53)) (distinct ?v_50 ?v_51)) (distinct ?v_50 ?v_52)) (distinct ?v_50 ?v_53)) (distinct ?v_51 ?v_52)) (distinct ?v_51 ?v_53)) (distinct ?v_52 ?v_53)) (distinct ?v_54 ?v_55)) (distinct ?v_54 ?v_56)) (distinct ?v_54 ?v_57)) (distinct ?v_54 ?v_58)) (distinct ?v_54 ?v_59)) (distinct ?v_54 ?v_60)) (distinct ?v_54 ?v_61)) (distinct ?v_54 ?v_62)) (distinct ?v_55 ?v_56)) (distinct ?v_55 ?v_57)) (distinct ?v_55 ?v_58)) (distinct ?v_55 ?v_59)) (distinct ?v_55 ?v_60)) (distinct ?v_55 ?v_61)) (distinct ?v_55 ?v_62)) (distinct ?v_56 ?v_57)) (distinct ?v_56 ?v_58)) (distinct ?v_56 ?v_59)) (distinct ?v_56 ?v_60)) (distinct ?v_56 ?v_61)) (distinct ?v_56 ?v_62)) (distinct ?v_57 ?v_58)) (distinct ?v_57 ?v_59)) (distinct ?v_57 ?v_60)) (distinct ?v_57 ?v_61)) (distinct ?v_57 ?v_62)) (distinct ?v_58 ?v_59)) (distinct ?v_58 ?v_60)) (distinct ?v_58 ?v_61)) (distinct ?v_58 ?v_62)) (distinct ?v_59 ?v_60)) (distinct ?v_59 ?v_61)) (distinct ?v_59 ?v_62)) (distinct ?v_60 ?v_61)) (distinct ?v_60 ?v_62)) (distinct ?v_61 ?v_62)) (distinct ?v_63 ?v_64)) (distinct ?v_63 ?v_65)) (distinct ?v_63 ?v_66)) (distinct ?v_63 ?v_67)) (distinct ?v_63 ?v_68)) (distinct ?v_63 ?v_69)) (distinct ?v_63 ?v_70)) (distinct ?v_63 ?v_71)) (distinct ?v_64 ?v_65)) (distinct ?v_64 ?v_66)) (distinct ?v_64 ?v_67)) (distinct ?v_64 ?v_68)) (distinct ?v_64 ?v_69)) (distinct ?v_64 ?v_70)) (distinct ?v_64 ?v_71)) (distinct ?v_65 ?v_66)) (distinct ?v_65 ?v_67)) (distinct ?v_65 ?v_68)) (distinct ?v_65 ?v_69)) (distinct ?v_65 ?v_70)) (distinct ?v_65 ?v_71)) (distinct ?v_66 ?v_67)) (distinct ?v_66 ?v_68)) (distinct ?v_66 ?v_69)) (distinct ?v_66 ?v_70)) (distinct ?v_66 ?v_71)) (distinct ?v_67 ?v_68)) (distinct ?v_67 ?v_69)) (distinct ?v_67 ?v_70)) (distinct ?v_67 ?v_71)) (distinct ?v_68 ?v_69)) (distinct ?v_68 ?v_70)) (distinct ?v_68 ?v_71)) (distinct ?v_69 ?v_70)) (distinct ?v_69 ?v_71)) (distinct ?v_70 ?v_71)) (or (or (or (or (or (or (or (or (= ?v_0 x1) (= ?v_0 x2)) (= ?v_0 x3)) (= ?v_0 x4)) (= ?v_0 x5)) (= ?v_0 x6)) (= ?v_0 x7)) (= ?v_0 x8)) (= ?v_0 x9))) (or (or (or (or (or (or (or (or (= ?v_1 x1) (= ?v_1 x2)) (= ?v_1 x3)) (= ?v_1 x4)) (= ?v_1 x5)) (= ?v_1 x6)) (= ?v_1 x7)) (= ?v_1 x8)) (= ?v_1 x9))) (or (or (or (or (or (or (or (or (= ?v_2 x1) (= ?v_2 x2)) (= ?v_2 x3)) (= ?v_2 x4)) (= ?v_2 x5)) (= ?v_2 x6)) (= ?v_2 x7)) (= ?v_2 x8)) (= ?v_2 x9))) (or (or (or (or (or (or (or (or (= ?v_3 x1) (= ?v_3 x2)) (= ?v_3 x3)) (= ?v_3 x4)) (= ?v_3 x5)) (= ?v_3 x6)) (= ?v_3 x7)) (= ?v_3 x8)) (= ?v_3 x9))) (or (or (or (or (or (or (or (or (= ?v_4 x1) (= ?v_4 x2)) (= ?v_4 x3)) (= ?v_4 x4)) (= ?v_4 x5)) (= ?v_4 x6)) (= ?v_4 x7)) (= ?v_4 x8)) (= ?v_4 x9))) (or (or (or (or (or (or (or (or (= ?v_5 x1) (= ?v_5 x2)) (= ?v_5 x3)) (= ?v_5 x4)) (= ?v_5 x5)) (= ?v_5 x6)) (= ?v_5 x7)) (= ?v_5 x8)) (= ?v_5 x9))) (or (or (or (or (or (or (or (or (= ?v_6 x1) (= ?v_6 x2)) (= ?v_6 x3)) (= ?v_6 x4)) (= ?v_6 x5)) (= ?v_6 x6)) (= ?v_6 x7)) (= ?v_6 x8)) (= ?v_6 x9))) (or (or (or (or (or (or (or (or (= ?v_7 x1) (= ?v_7 x2)) (= ?v_7 x3)) (= ?v_7 x4)) (= ?v_7 x5)) (= ?v_7 x6)) (= ?v_7 x7)) (= ?v_7 x8)) (= ?v_7 x9))) (or (or (or (or (or (or (or (or (= ?v_8 x1) (= ?v_8 x2)) (= ?v_8 x3)) (= ?v_8 x4)) (= ?v_8 x5)) (= ?v_8 x6)) (= ?v_8 x7)) (= ?v_8 x8)) (= ?v_8 x9))) (or (or (or (or (or (or (or (or (= ?v_9 x1) (= ?v_9 x2)) (= ?v_9 x3)) (= ?v_9 x4)) (= ?v_9 x5)) (= ?v_9 x6)) (= ?v_9 x7)) (= ?v_9 x8)) (= ?v_9 x9))) (or (or (or (or (or (or (or (or (= ?v_10 x1) (= ?v_10 x2)) (= ?v_10 x3)) (= ?v_10 x4)) (= ?v_10 x5)) (= ?v_10 x6)) (= ?v_10 x7)) (= ?v_10 x8)) (= ?v_10 x9))) (or (or (or (or (or (or (or (or (= ?v_11 x1) (= ?v_11 x2)) (= ?v_11 x3)) (= ?v_11 x4)) (= ?v_11 x5)) (= ?v_11 x6)) (= ?v_11 x7)) (= ?v_11 x8)) (= ?v_11 x9))) (or (or (or (or (or (or (or (or (= ?v_12 x1) (= ?v_12 x2)) (= ?v_12 x3)) (= ?v_12 x4)) (= ?v_12 x5)) (= ?v_12 x6)) (= ?v_12 x7)) (= ?v_12 x8)) (= ?v_12 x9))) (or (or (or (or (or (or (or (or (= ?v_13 x1) (= ?v_13 x2)) (= ?v_13 x3)) (= ?v_13 x4)) (= ?v_13 x5)) (= ?v_13 x6)) (= ?v_13 x7)) (= ?v_13 x8)) (= ?v_13 x9))) (or (or (or (or (or (or (or (or (= ?v_14 x1) (= ?v_14 x2)) (= ?v_14 x3)) (= ?v_14 x4)) (= ?v_14 x5)) (= ?v_14 x6)) (= ?v_14 x7)) (= ?v_14 x8)) (= ?v_14 x9))) (or (or (or (or (or (or (or (or (= ?v_15 x1) (= ?v_15 x2)) (= ?v_15 x3)) (= ?v_15 x4)) (= ?v_15 x5)) (= ?v_15 x6)) (= ?v_15 x7)) (= ?v_15 x8)) (= ?v_15 x9))) (or (or (or (or (or (or (or (or (= ?v_16 x1) (= ?v_16 x2)) (= ?v_16 x3)) (= ?v_16 x4)) (= ?v_16 x5)) (= ?v_16 x6)) (= ?v_16 x7)) (= ?v_16 x8)) (= ?v_16 x9))) (or (or (or (or (or (or (or (or (= ?v_17 x1) (= ?v_17 x2)) (= ?v_17 x3)) (= ?v_17 x4)) (= ?v_17 x5)) (= ?v_17 x6)) (= ?v_17 x7)) (= ?v_17 x8)) (= ?v_17 x9))) (or (or (or (or (or (or (or (or (= ?v_18 x1) (= ?v_18 x2)) (= ?v_18 x3)) (= ?v_18 x4)) (= ?v_18 x5)) (= ?v_18 x6)) (= ?v_18 x7)) (= ?v_18 x8)) (= ?v_18 x9))) (or (or (or (or (or (or (or (or (= ?v_19 x1) (= ?v_19 x2)) (= ?v_19 x3)) (= ?v_19 x4)) (= ?v_19 x5)) (= ?v_19 x6)) (= ?v_19 x7)) (= ?v_19 x8)) (= ?v_19 x9))) (or (or (or (or (or (or (or (or (= ?v_20 x1) (= ?v_20 x2)) (= ?v_20 x3)) (= ?v_20 x4)) (= ?v_20 x5)) (= ?v_20 x6)) (= ?v_20 x7)) (= ?v_20 x8)) (= ?v_20 x9))) (or (or (or (or (or (or (or (or (= ?v_21 x1) (= ?v_21 x2)) (= ?v_21 x3)) (= ?v_21 x4)) (= ?v_21 x5)) (= ?v_21 x6)) (= ?v_21 x7)) (= ?v_21 x8)) (= ?v_21 x9))) (or (or (or (or (or (or (or (or (= ?v_22 x1) (= ?v_22 x2)) (= ?v_22 x3)) (= ?v_22 x4)) (= ?v_22 x5)) (= ?v_22 x6)) (= ?v_22 x7)) (= ?v_22 x8)) (= ?v_22 x9))) (or (or (or (or (or (or (or (or (= ?v_23 x1) (= ?v_23 x2)) (= ?v_23 x3)) (= ?v_23 x4)) (= ?v_23 x5)) (= ?v_23 x6)) (= ?v_23 x7)) (= ?v_23 x8)) (= ?v_23 x9))) (or (or (or (or (or (or (or (or (= ?v_24 x1) (= ?v_24 x2)) (= ?v_24 x3)) (= ?v_24 x4)) (= ?v_24 x5)) (= ?v_24 x6)) (= ?v_24 x7)) (= ?v_24 x8)) (= ?v_24 x9))) (or (or (or (or (or (or (or (or (= ?v_25 x1) (= ?v_25 x2)) (= ?v_25 x3)) (= ?v_25 x4)) (= ?v_25 x5)) (= ?v_25 x6)) (= ?v_25 x7)) (= ?v_25 x8)) (= ?v_25 x9))) (or (or (or (or (or (or (or (or (= ?v_26 x1) (= ?v_26 x2)) (= ?v_26 x3)) (= ?v_26 x4)) (= ?v_26 x5)) (= ?v_26 x6)) (= ?v_26 x7)) (= ?v_26 x8)) (= ?v_26 x9))) (or (or (or (or (or (or (or (or (= ?v_27 x1) (= ?v_27 x2)) (= ?v_27 x3)) (= ?v_27 x4)) (= ?v_27 x5)) (= ?v_27 x6)) (= ?v_27 x7)) (= ?v_27 x8)) (= ?v_27 x9))) (or (or (or (or (or (or (or (or (= ?v_28 x1) (= ?v_28 x2)) (= ?v_28 x3)) (= ?v_28 x4)) (= ?v_28 x5)) (= ?v_28 x6)) (= ?v_28 x7)) (= ?v_28 x8)) (= ?v_28 x9))) (or (or (or (or (or (or (or (or (= ?v_29 x1) (= ?v_29 x2)) (= ?v_29 x3)) (= ?v_29 x4)) (= ?v_29 x5)) (= ?v_29 x6)) (= ?v_29 x7)) (= ?v_29 x8)) (= ?v_29 x9))) (or (or (or (or (or (or (or (or (= ?v_30 x1) (= ?v_30 x2)) (= ?v_30 x3)) (= ?v_30 x4)) (= ?v_30 x5)) (= ?v_30 x6)) (= ?v_30 x7)) (= ?v_30 x8)) (= ?v_30 x9))) (or (or (or (or (or (or (or (or (= ?v_31 x1) (= ?v_31 x2)) (= ?v_31 x3)) (= ?v_31 x4)) (= ?v_31 x5)) (= ?v_31 x6)) (= ?v_31 x7)) (= ?v_31 x8)) (= ?v_31 x9))) (or (or (or (or (or (or (or (or (= ?v_32 x1) (= ?v_32 x2)) (= ?v_32 x3)) (= ?v_32 x4)) (= ?v_32 x5)) (= ?v_32 x6)) (= ?v_32 x7)) (= ?v_32 x8)) (= ?v_32 x9))) (or (or (or (or (or (or (or (or (= ?v_33 x1) (= ?v_33 x2)) (= ?v_33 x3)) (= ?v_33 x4)) (= ?v_33 x5)) (= ?v_33 x6)) (= ?v_33 x7)) (= ?v_33 x8)) (= ?v_33 x9))) (or (or (or (or (or (or (or (or (= ?v_34 x1) (= ?v_34 x2)) (= ?v_34 x3)) (= ?v_34 x4)) (= ?v_34 x5)) (= ?v_34 x6)) (= ?v_34 x7)) (= ?v_34 x8)) (= ?v_34 x9))) (or (or (or (or (or (or (or (or (= ?v_35 x1) (= ?v_35 x2)) (= ?v_35 x3)) (= ?v_35 x4)) (= ?v_35 x5)) (= ?v_35 x6)) (= ?v_35 x7)) (= ?v_35 x8)) (= ?v_35 x9))) (or (or (or (or (or (or (or (or (= ?v_36 x1) (= ?v_36 x2)) (= ?v_36 x3)) (= ?v_36 x4)) (= ?v_36 x5)) (= ?v_36 x6)) (= ?v_36 x7)) (= ?v_36 x8)) (= ?v_36 x9))) (or (or (or (or (or (or (or (or (= ?v_37 x1) (= ?v_37 x2)) (= ?v_37 x3)) (= ?v_37 x4)) (= ?v_37 x5)) (= ?v_37 x6)) (= ?v_37 x7)) (= ?v_37 x8)) (= ?v_37 x9))) (or (or (or (or (or (or (or (or (= ?v_38 x1) (= ?v_38 x2)) (= ?v_38 x3)) (= ?v_38 x4)) (= ?v_38 x5)) (= ?v_38 x6)) (= ?v_38 x7)) (= ?v_38 x8)) (= ?v_38 x9))) (or (or (or (or (or (or (or (or (= ?v_39 x1) (= ?v_39 x2)) (= ?v_39 x3)) (= ?v_39 x4)) (= ?v_39 x5)) (= ?v_39 x6)) (= ?v_39 x7)) (= ?v_39 x8)) (= ?v_39 x9))) (or (or (or (or (or (or (or (or (= ?v_40 x1) (= ?v_40 x2)) (= ?v_40 x3)) (= ?v_40 x4)) (= ?v_40 x5)) (= ?v_40 x6)) (= ?v_40 x7)) (= ?v_40 x8)) (= ?v_40 x9))) (or (or (or (or (or (or (or (or (= ?v_41 x1) (= ?v_41 x2)) (= ?v_41 x3)) (= ?v_41 x4)) (= ?v_41 x5)) (= ?v_41 x6)) (= ?v_41 x7)) (= ?v_41 x8)) (= ?v_41 x9))) (or (or (or (or (or (or (or (or (= ?v_42 x1) (= ?v_42 x2)) (= ?v_42 x3)) (= ?v_42 x4)) (= ?v_42 x5)) (= ?v_42 x6)) (= ?v_42 x7)) (= ?v_42 x8)) (= ?v_42 x9))) (or (or (or (or (or (or (or (or (= ?v_43 x1) (= ?v_43 x2)) (= ?v_43 x3)) (= ?v_43 x4)) (= ?v_43 x5)) (= ?v_43 x6)) (= ?v_43 x7)) (= ?v_43 x8)) (= ?v_43 x9))) (or (or (or (or (or (or (or (or (= ?v_44 x1) (= ?v_44 x2)) (= ?v_44 x3)) (= ?v_44 x4)) (= ?v_44 x5)) (= ?v_44 x6)) (= ?v_44 x7)) (= ?v_44 x8)) (= ?v_44 x9))) (or (or (or (or (or (or (or (or (= ?v_45 x1) (= ?v_45 x2)) (= ?v_45 x3)) (= ?v_45 x4)) (= ?v_45 x5)) (= ?v_45 x6)) (= ?v_45 x7)) (= ?v_45 x8)) (= ?v_45 x9))) (or (or (or (or (or (or (or (or (= ?v_46 x1) (= ?v_46 x2)) (= ?v_46 x3)) (= ?v_46 x4)) (= ?v_46 x5)) (= ?v_46 x6)) (= ?v_46 x7)) (= ?v_46 x8)) (= ?v_46 x9))) (or (or (or (or (or (or (or (or (= ?v_47 x1) (= ?v_47 x2)) (= ?v_47 x3)) (= ?v_47 x4)) (= ?v_47 x5)) (= ?v_47 x6)) (= ?v_47 x7)) (= ?v_47 x8)) (= ?v_47 x9))) (or (or (or (or (or (or (or (or (= ?v_48 x1) (= ?v_48 x2)) (= ?v_48 x3)) (= ?v_48 x4)) (= ?v_48 x5)) (= ?v_48 x6)) (= ?v_48 x7)) (= ?v_48 x8)) (= ?v_48 x9))) (or (or (or (or (or (or (or (or (= ?v_49 x1) (= ?v_49 x2)) (= ?v_49 x3)) (= ?v_49 x4)) (= ?v_49 x5)) (= ?v_49 x6)) (= ?v_49 x7)) (= ?v_49 x8)) (= ?v_49 x9))) (or (or (or (or (or (or (or (or (= ?v_50 x1) (= ?v_50 x2)) (= ?v_50 x3)) (= ?v_50 x4)) (= ?v_50 x5)) (= ?v_50 x6)) (= ?v_50 x7)) (= ?v_50 x8)) (= ?v_50 x9))) (or (or (or (or (or (or (or (or (= ?v_51 x1) (= ?v_51 x2)) (= ?v_51 x3)) (= ?v_51 x4)) (= ?v_51 x5)) (= ?v_51 x6)) (= ?v_51 x7)) (= ?v_51 x8)) (= ?v_51 x9))) (or (or (or (or (or (or (or (or (= ?v_52 x1) (= ?v_52 x2)) (= ?v_52 x3)) (= ?v_52 x4)) (= ?v_52 x5)) (= ?v_52 x6)) (= ?v_52 x7)) (= ?v_52 x8)) (= ?v_52 x9))) (or (or (or (or (or (or (or (or (= ?v_53 x1) (= ?v_53 x2)) (= ?v_53 x3)) (= ?v_53 x4)) (= ?v_53 x5)) (= ?v_53 x6)) (= ?v_53 x7)) (= ?v_53 x8)) (= ?v_53 x9))) (or (or (or (or (or (or (or (or (= ?v_54 x1) (= ?v_54 x2)) (= ?v_54 x3)) (= ?v_54 x4)) (= ?v_54 x5)) (= ?v_54 x6)) (= ?v_54 x7)) (= ?v_54 x8)) (= ?v_54 x9))) (or (or (or (or (or (or (or (or (= ?v_55 x1) (= ?v_55 x2)) (= ?v_55 x3)) (= ?v_55 x4)) (= ?v_55 x5)) (= ?v_55 x6)) (= ?v_55 x7)) (= ?v_55 x8)) (= ?v_55 x9))) (or (or (or (or (or (or (or (or (= ?v_56 x1) (= ?v_56 x2)) (= ?v_56 x3)) (= ?v_56 x4)) (= ?v_56 x5)) (= ?v_56 x6)) (= ?v_56 x7)) (= ?v_56 x8)) (= ?v_56 x9))) (or (or (or (or (or (or (or (or (= ?v_57 x1) (= ?v_57 x2)) (= ?v_57 x3)) (= ?v_57 x4)) (= ?v_57 x5)) (= ?v_57 x6)) (= ?v_57 x7)) (= ?v_57 x8)) (= ?v_57 x9))) (or (or (or (or (or (or (or (or (= ?v_58 x1) (= ?v_58 x2)) (= ?v_58 x3)) (= ?v_58 x4)) (= ?v_58 x5)) (= ?v_58 x6)) (= ?v_58 x7)) (= ?v_58 x8)) (= ?v_58 x9))) (or (or (or (or (or (or (or (or (= ?v_59 x1) (= ?v_59 x2)) (= ?v_59 x3)) (= ?v_59 x4)) (= ?v_59 x5)) (= ?v_59 x6)) (= ?v_59 x7)) (= ?v_59 x8)) (= ?v_59 x9))) (or (or (or (or (or (or (or (or (= ?v_60 x1) (= ?v_60 x2)) (= ?v_60 x3)) (= ?v_60 x4)) (= ?v_60 x5)) (= ?v_60 x6)) (= ?v_60 x7)) (= ?v_60 x8)) (= ?v_60 x9))) (or (or (or (or (or (or (or (or (= ?v_61 x1) (= ?v_61 x2)) (= ?v_61 x3)) (= ?v_61 x4)) (= ?v_61 x5)) (= ?v_61 x6)) (= ?v_61 x7)) (= ?v_61 x8)) (= ?v_61 x9))) (or (or (or (or (or (or (or (or (= ?v_62 x1) (= ?v_62 x2)) (= ?v_62 x3)) (= ?v_62 x4)) (= ?v_62 x5)) (= ?v_62 x6)) (= ?v_62 x7)) (= ?v_62 x8)) (= ?v_62 x9))) (or (or (or (or (or (or (or (or (= ?v_63 x1) (= ?v_63 x2)) (= ?v_63 x3)) (= ?v_63 x4)) (= ?v_63 x5)) (= ?v_63 x6)) (= ?v_63 x7)) (= ?v_63 x8)) (= ?v_63 x9))) (or (or (or (or (or (or (or (or (= ?v_64 x1) (= ?v_64 x2)) (= ?v_64 x3)) (= ?v_64 x4)) (= ?v_64 x5)) (= ?v_64 x6)) (= ?v_64 x7)) (= ?v_64 x8)) (= ?v_64 x9))) (or (or (or (or (or (or (or (or (= ?v_65 x1) (= ?v_65 x2)) (= ?v_65 x3)) (= ?v_65 x4)) (= ?v_65 x5)) (= ?v_65 x6)) (= ?v_65 x7)) (= ?v_65 x8)) (= ?v_65 x9))) (or (or (or (or (or (or (or (or (= ?v_66 x1) (= ?v_66 x2)) (= ?v_66 x3)) (= ?v_66 x4)) (= ?v_66 x5)) (= ?v_66 x6)) (= ?v_66 x7)) (= ?v_66 x8)) (= ?v_66 x9))) (or (or (or (or (or (or (or (or (= ?v_67 x1) (= ?v_67 x2)) (= ?v_67 x3)) (= ?v_67 x4)) (= ?v_67 x5)) (= ?v_67 x6)) (= ?v_67 x7)) (= ?v_67 x8)) (= ?v_67 x9))) (or (or (or (or (or (or (or (or (= ?v_68 x1) (= ?v_68 x2)) (= ?v_68 x3)) (= ?v_68 x4)) (= ?v_68 x5)) (= ?v_68 x6)) (= ?v_68 x7)) (= ?v_68 x8)) (= ?v_68 x9))) (or (or (or (or (or (or (or (or (= ?v_69 x1) (= ?v_69 x2)) (= ?v_69 x3)) (= ?v_69 x4)) (= ?v_69 x5)) (= ?v_69 x6)) (= ?v_69 x7)) (= ?v_69 x8)) (= ?v_69 x9))) (or (or (or (or (or (or (or (or (= ?v_70 x1) (= ?v_70 x2)) (= ?v_70 x3)) (= ?v_70 x4)) (= ?v_70 x5)) (= ?v_70 x6)) (= ?v_70 x7)) (= ?v_70 x8)) (= ?v_70 x9))) (or (or (or (or (or (or (or (or (= ?v_71 x1) (= ?v_71 x2)) (= ?v_71 x3)) (= ?v_71 x4)) (= ?v_71 x5)) (= ?v_71 x6)) (= ?v_71 x7)) (= ?v_71 x8)) (= ?v_71 x9))) (distinct x1 x2)) (distinct x1 x3)) (distinct x1 x4)) (distinct x1 x5)) (distinct x1 x6)) (distinct x1 x7)) (distinct x1 x8)) (distinct x1 x9)) (distinct x2 x3)) (distinct x2 x4)) (distinct x2 x5)) (distinct x2 x6)) (distinct x2 x7)) (distinct x2 x8)) (distinct x2 x9)) (distinct x3 x4)) (distinct x3 x5)) (distinct x3 x6)) (distinct x3 x7)) (distinct x3 x8)) (distinct x3 x9)) (distinct x4 x5)) (distinct x4 x6)) (distinct x4 x7)) (distinct x4 x8)) (distinct x4 x9)) (distinct x5 x6)) (distinct x5 x7)) (distinct x5 x8)) (distinct x5 x9)) (distinct x6 x7)) (distinct x6 x8)) (distinct x6 x9)) (distinct x7 x8)) (distinct x7 x9)) (distinct x8 x9)) (<= 0 x1)) (< x1 10)) (<= 0 x2)) (< x2 10)) (<= 0 x3)) (< x3 10)) (<= 0 x4)) (< x4 10)) (<= 0 x5)) (< x5 10)) (<= 0 x6)) (< x6 10)) (<= 0 x7)) (< x7 10)) (<= 0 x8)) (< x8 10)) (<= 0 x9)) (< x9 10)) (= (hash_1 (hash_1 (hash_8 (ite (< ?v_72 10) ?v_72 x1)))) (hash_1 (hash_1 (hash_8 (ite (< ?v_73 10) ?v_73 x1))))))))
(check-sat)
(exit)
