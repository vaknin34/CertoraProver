(set-logic UFLIA)

(declare-fun f (Int) Int)
(declare-const c Int)
(declare-const d Int)

(assert (and (= c 3) (= d 4) (distinct (f (+ c 1)) (f d))))

(check-sat)
