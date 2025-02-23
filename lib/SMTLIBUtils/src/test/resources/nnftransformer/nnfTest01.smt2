(set-logic QF_UF)

(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)

(assert (=> A B))
(assert (or (not A) B))

(assert (= A B))
(assert (and (or (not A) B) (or A (not B))))

(assert (not (or A B)))
(assert (and (not A) (not B)))

(assert (not (and A B)))
(assert (or (not A) (not B)))

(assert (not (not A)))
(assert A)

(assert (not (not (not A))))
(assert (not A))

