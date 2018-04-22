; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; FLOATING-POINT OPTIMIZATION:
;     OptiMathSAT supports Floating-Point optimization.
;
;     The domain of any FP Objective is restricted so as
;     to exclude the NaN FP value. This might transform
;     a satisfiable SMT problem into an unsatisfiable
;     OMT problem when the only valid domain value of 
;     a given FP Term is NaN. If necessary, one can test
;     for equality with NaN prior to any optimization.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :opt.priority box)

;
; PROBLEM
;
(define-fun _m_inf () (_ FloatingPoint 8 24) (fp #b1 #b11111111 #b00000000000000000000000))
(define-fun _m_ten () (_ FloatingPoint 8 24) (fp #b1 #b10000010 #b01000000000000000000000))
(define-fun _zero  () (_ FloatingPoint 8 24) (fp #b0 #b00000000 #b00000000000000000000000))
(define-fun _p_ten () (_ FloatingPoint 8 24) (fp #b0 #b10000010 #b01000000000000000000000))
(define-fun _p_inf () (_ FloatingPoint 8 24) (fp #b0 #b11111111 #b00000000000000000000000))
(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(assert (and
        (fp.leq _m_ten x0)
        (fp.leq x0 _p_ten)
))
(assert (= x1 _zero))
(assert (= x2 (_ NaN 8 24)))
(assert (and
        (fp.leq _m_inf x3)
        (fp.leq x3 _p_inf)
))

;
; GOALS
;
(minimize x0)
(maximize x0)
(minimize x1)
(minimize x2)                       ; CONSTRAINT: NaN is UNSAT for any objective
(minimize x3 :lower _m_ten :upper _p_ten)
(maximize x3 :lower _m_ten :upper _p_ten)

;
;  OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)

