(set-logic AUFNIA)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (> x 5))
(check-sat) ; sat

(push 1)
(assert (= x 5))
(check-sat) ; unsat
(pop 1)

(check-sat) ; sat

(assert (= (+ x y) 13))
(check-sat) ; sat

(push 2)
(assert (> y 10))
(check-sat) ; unsat
(pop 1)
(check-sat) ; sat
(assert (> y 1))
(check-sat) ; sat
(assert (> y 10))
(check-sat) ; unsat
(pop 1)
(check-sat) ; sat


