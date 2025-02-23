(set-logic UFLIA)

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)

(assert (and (or A B) (or (not C) D)))

(check-sat)
