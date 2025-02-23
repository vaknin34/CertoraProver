(set-logic AUFLIA)

(declare-fun f (Int) Int)
(declare-const c Int)
(declare-const d Int)
(declare-const d Int)

(declare-const i Int)

(declare-const a (Array Int Bool))

(assert (= c ((as f Bool) d)))


; select (Array A B) x A -> B
; instantiateResultSort(Bool)
; select (Array A Bool) x A -> Bool
; instantiateParamSorts((Array Int Bool), Int)
; select (Array A Bool) x A -> Bool




(declare-sort (F 2))

; (F Int A)


; f(x, 15)
; f(12, y)

(assert (= c ((as select Bool) ar i)))

(check-sat)
