(set-logic QF_LIA)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (> a 10))
(assert (< b 5))
(assert (= (+ a b) c))

(check-sat)
(get-model)
