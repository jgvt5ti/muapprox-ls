(set-logic HORN)
(set-info :source |
  Benchmark: /home/katsura/hflmc2/benchmark/ml/test_safe_2019/adt/divide_list2.ml
  Generated by MoCHi
|)
(set-info :status unknown)
(declare-fun |fail_169[0:0]| ( Int) Bool)
(declare-fun |length[0:2][0:0]| ( Int  Int) Bool)
(declare-fun |length[0:0]| ( Int) Bool)
(declare-fun |divide[0:3][0:2]| ( Int  Int  Int  Int) Bool)
(declare-fun |divide[0:1]| ( Int  Int) Bool)
(declare-fun |make_int_list[0:2][0:0]| ( Int  Int  Int) Bool)
(declare-fun |make_int_list[0:1]| ( Int  Int) Bool)
(assert (not (exists ((x0 Int)) (|fail_169[0:0]| x0))))
(assert (forall ((x0 Int)(x5 Int)(x8 Int)(x7 Int)(x6 Int)(x4 Int)(x2 Int)(x3 Int)(x1 Int)(var1146 Int)) (=> (and (|length[0:2][0:0]| x4 x8) (and (|length[0:2][0:0]| x2 x5) (and (|length[0:2][0:0]| x3 x6) (and (|length[0:2][0:0]| x2 x7) (and (|divide[0:3][0:2]| x1 x2 x3 x4) (and (|make_int_list[0:2][0:0]| x1 var1146 x2) (and (<= (+ 1 x5) x8) (>= x7 x6)))))))) (|fail_169[0:0]| x0))))
(assert (forall ((x1 Int)(x2 Int)(var1147 Int)(var1148 Int)) (=> (and (|length[0:2][0:0]| var1147 var1148) (and (|length[0:0]| x1) (and (>= x1 1) (and (= (+ 1 var1147) x1) (= x2 (+ 1 var1148)))))) (|length[0:2][0:0]| x1 x2))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x1) (and (= x0 0) (<= x1 0))) (|length[0:2][0:0]| x1 x0))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x0) (and (= (+ 1 x1) x0) (>= x0 1))) (|length[0:0]| x1))))
(assert (forall ((x3 Int)(x5 Int)(x4 Int)(x1 Int)(x6 Int)(x2 Int)(x0 Int)(var1149 Int)) (=> (and (|length[0:2][0:0]| x1 x6) (and (|length[0:2][0:0]| x2 x4) (and (|length[0:2][0:0]| x1 x5) (and (|divide[0:3][0:2]| x0 x1 x2 x3) (and (|make_int_list[0:2][0:0]| x0 var1149 x1) (>= x5 x4)))))) (|length[0:0]| x3))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x1) (and (= x0 0) (<= x1 0))) (|length[0:2][0:0]| x1 x0))))
(assert (forall ((x1 Int)(x4 Int)(x5 Int)(x2 Int)(x0 Int)(x3 Int)(var1150 Int)) (=> (and (|length[0:2][0:0]| x2 x5) (and (|length[0:2][0:0]| x1 x4) (and (|divide[0:3][0:2]| x0 x1 x2 x3) (and (|make_int_list[0:2][0:0]| x0 var1150 x1) (>= x4 x5))))) (|length[0:0]| x1))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x1) (and (= x0 0) (<= x1 0))) (|length[0:2][0:0]| x1 x0))))
(assert (forall ((x2 Int)(x1 Int)(x4 Int)(x0 Int)(x3 Int)(var1151 Int)) (=> (and (|length[0:2][0:0]| x1 x4) (and (|divide[0:3][0:2]| x0 x1 x2 x3) (|make_int_list[0:2][0:0]| x0 var1151 x1))) (|length[0:0]| x2))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x1) (and (= x0 0) (<= x1 0))) (|length[0:2][0:0]| x1 x0))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)(var1152 Int)) (=> (and (|divide[0:3][0:2]| x0 x1 x2 x3) (|make_int_list[0:2][0:0]| x0 var1152 x1)) (|length[0:0]| x1))))
(assert (forall ((x2 Int)(x3 Int)(x0 Int)(x1 Int)) (=> (and (|divide[0:1]| x2 x3) (and (= x0 0) (and (= x1 0) (<= x3 0)))) (|divide[0:3][0:2]| x2 x3 x0 x1))))
(assert (forall ((x0 Int)(x1 Int)(var1153 Int)) (=> (|make_int_list[0:2][0:0]| x0 var1153 x1) (|divide[0:1]| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|make_int_list[0:1]| x0 x1) (= x2 0)) (|make_int_list[0:2][0:0]| x0 x1 x2))))
(assert (forall ((x1 Int)(x0 Int)) (|make_int_list[0:1]| x1 x0)))
(check-sat)
(get-model)
(exit)
