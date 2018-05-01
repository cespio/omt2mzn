(set-option :opt.priority lex)

;
; PROBLEM
;

(set-logic QF_LIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)

(assert (< x2 6))
(assert (>= (+ (* 3 x2) x1) 3))
(assert (<= (+ (* 2 x1) (- x2)) 6))
(assert (<= (+ (* 2 x1) x2) 10))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= (+ (* 3 x2) x1) 3))

(maximize (- (* 4 x2) x1))
(minimize (+ (* 3 x1) x2))

(check-sat)
(get-objectives)