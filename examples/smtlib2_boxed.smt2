; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; WARNING:
;     OptiMathSAT and Z3 have different default behaviours
;     when multiple objectives are optimized in the same
;     formula. Z3 handles them lexicographically, whereas
;     OptiMathSAT handles them in boxed (multi-independent) mode.
;     Therefore, the following option should be correctly
;     set on any boxed/multi-independent formula:
;
;         (set-option :opt.priority box)
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :opt.priority box)

;
; PROBLEM
;
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and
        (<= 42 x)
        (<= y x)
))

;
; GOALS
;
(minimize x)
(maximize y)
(maximize z :upper 50)

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)
