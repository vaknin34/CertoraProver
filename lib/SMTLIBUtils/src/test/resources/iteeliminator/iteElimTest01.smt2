(set-logic QF_UF)

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(declare-const E Bool)
(declare-const F Bool)

(declare-sort S 0)
(declare-const x S)
(declare-const y S)
(declare-const z S)
(declare-fun f (S S) S)
(declare-fun g (S) S)

(assert (ite A B C))
(assert (and (or (not A) B) (or A C)))
(assert (or (and A B) (and (not A) C)))

(assert (and A (or B (not (and C (ite D E F))))))
(assert (and A (or B (not (and C (and (or (not D) E) (or D F)))))))
(assert (and A (or B (not (and C (or (and D E) (and (not D) F)))))))

(assert (ite A B (and D (or E (not F)))))
(assert (and (or (not A) B) (or A (and D (or E (not F))))))
(assert (or (and A B) (and (not A) (and D (or E (not F))))))

(assert (ite (ite D E F) B C))
(assert (and (or (not (and (or (not D) E) (or D F))) B) (or (and (or (not D) E) (or D F)) C)))
(assert (or (and (or (and D E) (and (not D) F)) B) (and (not (or (and D E) (and (not D) F))) C)))

(assert (= x (ite A y z)))
(assert (and (or (not A) (= x y)) (or A (= x z))))
(assert (or (and A (= x y)) (and (not A) (= x z))))

