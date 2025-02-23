(set-logic AUFLIA)

(declare-fun f (Int) Int)
(declare-const c Int)
(declare-const d Int)

(assert (= c (f d)))

(check-sat)
