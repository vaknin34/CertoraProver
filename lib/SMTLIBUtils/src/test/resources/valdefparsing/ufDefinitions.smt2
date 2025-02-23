(set-option :produce-models true)
(set-logic ALL)

(declare-fun foo (Int) Int)
(declare-fun bar (Int) Int)
(declare-const x Int)
(declare-const y Int)

(assert (distinct x y))
(assert (= x (foo 12)))
(assert (= y (foo 37)))

(check-sat)
; (get-value (foo bar))
