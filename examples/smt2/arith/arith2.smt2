(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (and (<= x 42) (>= x 0) (>= y 42) (= (+ x y) 50)))
(check-sat)
(get-model)
