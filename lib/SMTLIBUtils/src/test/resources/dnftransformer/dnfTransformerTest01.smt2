(set-logic QF_UF)

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(declare-const E Bool)
(declare-const F Bool)


(assert (and A B C))
(assert (and A B C))

(assert (or A B C))
(assert (or A B C))

(assert (or (and A D) B C))
(assert (or (and A D) B C))

(assert (and (or A D) B C))
(assert (or (and A B C) (and D B C)))

(assert (and (or A D) B (or (not A) E)))
(assert (or (and A B (not A)) (and A B E) (and D B (not A)) (and D B E)))

