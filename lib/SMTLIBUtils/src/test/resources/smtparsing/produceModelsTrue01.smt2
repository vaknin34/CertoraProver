(set-logic AUFLIA)
(set-option :produce-models true)
(declare-fun f (Int) Int)
(declare-const c Int)
(declare-const d Int)
(declare-const d Int)
(declare-const i Int)
(declare-const a (Array Int Bool))
(assert (= c (f d)))
(check-sat)
