; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; MINMAX/MAXMIN:
;     These smtlib2 extensions are only supported by OptiMathSAT.
;     These are syntactic-sugar functions that make it easier
;     to define minmax/maxmin objectives.
;     The syntax is:
;
;         (minmax <term_1> ... <term_n>)
;         (maxmin <term_1> ... <term_n>)
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :opt.priority box)

;
; PROBLEM
;
(declare-fun l0 () Int)
(declare-fun l1 () Int)
(declare-fun l2 () Int)
(assert (< l0 10))
(assert (< l1 12))
(assert (< l2 14))

;
; GOAL
;
(minmax l0 l1 l2 :id my_cost)

;
; OPTIMIZATION
;
(check-sat)
(get-objectives)

(exit)
