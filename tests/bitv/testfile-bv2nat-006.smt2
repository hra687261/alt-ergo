(set-logic ALL)
(declare-const x (_ BitVec 1024))
(declare-const y (_ BitVec 1024))
(assert (= (bv2nat x) (bv2nat y)))
(assert (distinct x y))
(check-sat)
