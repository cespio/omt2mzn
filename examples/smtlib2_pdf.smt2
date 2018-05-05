(set-option :produce-models true) ; enable print model
(set-logic QF_LIA)
(declare-fun production_cost () Int)
(declare-fun q0 () Int)
; machine ’i’ production load
(declare-fun q1 () Int)
(declare-fun q2 () Int)
(declare-fun q3 () Int)
(declare-fun m0 () Bool)
; machine ’i’ is used
(declare-fun m1 () Bool)
(declare-fun m2 () Bool)
(declare-fun m3 () Bool)
(declare-fun used_machines () Int)
(assert (<= 1100 (+ q0 q1 q2 q3))) ; set goods quantity
(assert (and
; set goods produced per machine
(and (<= 0 q0) (<= q0 800)) (and (<= 0 q1) (<= q1 500))
(and (<= 0 q2) (<= q2 600)) (and (<= 0 q3) (<= q3 200))
))
(assert (and
; set machine ‘used‘ flag
(=> (< 0 q0) m0) (=> (< 0 q1) m1)
(=> (< 0 q2) m2) (=> (< 0 q3) m3)
))
(assert (= production_cost (+ (* q0 8) (* q1 9) (* q2 9) (* q3 5)) ))
(assert-soft (not m0) :id used_machines)
(assert-soft (not m1) :id used_machines)
(assert-soft (not m2) :id used_machines)
(assert-soft (not m3) :id used_machines)
(push 1)
; optimize (A) and (B) lexicographically
(minimize production_cost)
(minimize used_machines)
(set-option :opt.priority lex)
(check-sat)
(get-objectives)
(pop 1)
; optimize (C), use :id to print model value
(minimize (+ 10 (* (/ 785 10) (+ (* 2 used_machines) 8))) :id total_cost)
(set-option :opt.priority box)
(check-sat)