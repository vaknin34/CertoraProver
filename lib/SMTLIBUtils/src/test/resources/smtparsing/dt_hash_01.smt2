(set-logic QF_UFDTNIA)

(declare-const i Int)

(declare-datatypes ((hash 0)) (((symbol (value Int)) (hash (inner hash) (offset Int)))))

(assert (= (hash (symbol 5) i) (hash (symbol i) 3)))

(check-sat)
