; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; PROBLEM
;
(declare-fun x () Real)

(push 1)
(assert (<= 5 x))
(minimize x)
(check-sat)
(get-objectives)
(pop 1)

(push 1)
(maximize x)
(check-sat)
(get-objectives)
(pop 1)

(check-sat)
(get-objectives)

(exit)
