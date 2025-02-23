(set-logic AUFLIA)
(declare-fun f (Int) Int)(declare-const c Int) (declare-const d Int)
; a comment
(assert (= c (f d))) ; another comment

(check-sat)
