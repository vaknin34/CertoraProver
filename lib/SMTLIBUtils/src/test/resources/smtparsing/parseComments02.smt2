(set-logic AUFLIA)
(declare-fun f (Int) Int)(declare-const c Int) (declare-const d Int)
; a comment
(assert (= c ; another comment
   (f d)))

(check-sat)
