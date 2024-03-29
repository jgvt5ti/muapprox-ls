; pcsatの古いバージョンではsat, 新しいバージョンではunsatとなった。
; z3で解いた結果は "unsat" となった
; unsatが正しいと思われる
(declare-fun X1 (Int Int) Bool)
(declare-fun X2 (Int Int) Bool)
(declare-fun X3 (Int Int) Bool)
(declare-fun X4 (Int Int) Bool)
(declare-fun X7 (Int Int) Bool)
(declare-fun X22 () Bool)
(declare-fun X23 (Int) Bool)
(declare-fun X24 (Int Int) Bool)
(declare-fun X32 (Int Int Int) Bool)
(assert (forall ((x40 Int)(x41 Int)) (=> (not (=  x40 x41)) (X1  x41 x40))))
(assert (forall ((x37 Int)(x39 Int)) (=> (X4  x39 x37) (X3  x39 x37))))
(assert (forall ((x28 Int)(x37 Int)(x38 Int)) (=> (X2  x38 x37) (or (X4  x38 x37) (X3  x28 x37)))))
(assert (forall ((x35 Int)(x36 Int)) (=> (and (X32  x36 x36 x35) (X7  x36 (-  x35 1))) (X7  x36 x35))))
(assert (forall ((x35 Int)(x36 Int)) (=> (<  x35 0) (X7  x36 x35))))
(assert (forall ((e6 Int)(n7 Int)(x34 Int)) (=> (X3  x34 e6) (X32  x34 n7 e6))))
(assert (forall ((e6 Int)(n7 Int)(x28 Int)(x33 Int)) (=> (X1  x33 n7) (or (X2  x33 e6) (X32  x28 n7 e6)))))
(assert (forall ((n4 Int)) (=> (X23  n4) X22)))
(assert (forall ((e5 Int)(n4 Int)) (=> (X24  e5 n4) (X23  n4))))
(assert (forall ((e5 Int)(n4 Int)) (=> (and (>=  e5 (+  1 (*  1 n4))) (and (>=  e5 (+  1 (*  (-  0 1) n4))) (X7  n4 e5))) (X24  e5 n4))))
(assert (=> X22 false))
(check-sat)
    