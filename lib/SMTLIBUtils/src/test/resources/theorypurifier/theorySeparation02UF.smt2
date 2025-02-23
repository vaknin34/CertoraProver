(set-logic QF_UF)

(declare-sort PInt 0)
(declare-fun f (PInt) PInt)
(declare-const c PInt)
(declare-const d PInt)
(declare-const sh1 PInt)
(declare-const shConst1 PInt)

;(assert (and (= c 3) (= (+ c 1) sh1) (= shConst1 4)))
(assert (distinct (f sh1) (f shConst1)))

(check-sat)
