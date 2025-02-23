(set-logic QF_UFLIA)

(declare-fun f (Int) Int)
(declare-const c Int)
(declare-const d Int)
(declare-const sh1 Int)
(declare-const shConst1 Int)

(assert (and (= c 3) (= (+ c 1) sh1) (= shConst1 4)))
(assert (distinct (f sh1) (f shConst1)))

(check-sat)
