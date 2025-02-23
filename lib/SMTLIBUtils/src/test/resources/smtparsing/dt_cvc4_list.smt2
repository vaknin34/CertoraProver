(set-logic QF_UFDTNIA)

(declare-datatypes ((list 0))
  (((cons (head Int) (tail list)) (nil))))
(declare-fun a () list)
(declare-fun b () list)
(assert (and (= (tail a) b) (not ((_ is nil) b)) (> (head b) 0)))
(check-sat)

(check-sat)
