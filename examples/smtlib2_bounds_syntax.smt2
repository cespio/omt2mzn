; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; OBJECTIVE BOUNDS:
;     This file contains a variety of syntax examples which
;     depict upper/lower bound usage with OptiMathSAT.
;
;     For more details about lower/upper bounds semantics
;     and handling, please consult:
;
;         smtlib2_bounds_semantics.smt2
;
;     Rules:
;     - a bound must be of the same type of the objective
;       function, or of a compatible type (e.g. lia/lar)
;     - a bound must be a constant value
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :opt.priority box)

;
; PROBLEM
;
(declare-fun x () Real)
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ FloatingPoint 2 5))

(define-fun int_bound  () Int                                     14)
(define-fun real_bound () Real                               (/ 5 2))
(define-fun bv_bound   () (_ BitVec 4)                        #b1001)
(define-fun fp_bound   () (_ FloatingPoint 2 5) (fp #b0 #b01 #b0100))

;
; LAR/LIA
;
;;; SAT
(minimize x                                       :id unbounded_x)
(minimize x :lower (+ 5 (/ 3 2))                  :id min_sum_x)
(minimize x :lower int_bound                      :id min_int_x)
(maximize x                     :upper int_bound  :id max_int_x)
(minimize x :lower real_bound                     :id min_real_x)
(maximize x                     :upper real_bound :id max_real_x)
(minimize x :lower (- (/ 21 7)) :upper (/ 21 7)   :id min_const_x)
(maximize x :lower (- (/ 21 8)) :upper 3          :id max_const_x)
;;; UNSAT (empty interval)
(minimize x :lower 10           :upper 1          :id unsat_1_x)
(minimize x :lower 10           :upper 10         :id unsat_2_x)

;
; BV
;
;;; SAT
(minimize y                                                           :id unbounded_y)
(minimize y :lower bv_bound                                           :id min_ubv_y)
(maximize y                            :upper bv_bound                :id max_ubv_y)
(minimize y :lower bv_bound                                   :signed :id min_sbv_y)
(maximize y                            :upper bv_bound        :signed :id max_sbv_y)
(minimize y :lower ((_ to_bv 4) 0)     :upper ((_ to_bv 4) 5)         :id min_const_ubv_y)
(maximize y :lower #b0000              :upper ((_ to_bv 4) 5)         :id max_const_ubv_y)
(minimize y :lower ((_ to_bv 4) (- 5)) :upper ((_ to_bv 4) 5) :signed :id min_const_sbv_y)
(maximize y :lower ((_ to_bv 4) (- 5)) :upper ((_ to_bv 4) 5) :signed :id max_const_sbv_y)
;;; UNSAT (empty interval)
(minimize y :lower ((_ to_bv 4) (- 5)) :upper ((_ to_bv 4) 5)         :id unsat_1_y)
(minimize y :lower #b0111              :upper #b0001                  :id unsat_2_y)
(minimize y :lower #b0111              :upper #b0111                  :id unsat_3_y)
(minimize y :lower #b0000              :upper #b1111          :signed :id unsat_4_y)

;
; FP
;
;;; SAT
(minimize z                                                                        :id unbounded_z)
(minimize z :lower fp_bound                                                        :id min_fp_z)
(maximize z                                        :upper fp_bound                 :id max_fp_z)
(minimize z :lower ((_ to_fp 2 5) RNE (- 0.2))     :upper (fp #b0 #b10 #b0000)     :id min_const_fp_z)
(maximize z :lower ((_ to_fp 2 5) RNE (- (/ 1 5))) :upper ((_ to_fp 2 5) RNE 1.45) :id max_const_fp_z)
;;; UNSAT (empty interval)
(minimize z :lower ((_ to_fp 2 5) RNE 2)           :upper ((_ to_fp 2 5) RNE 1)    :id unsat_1_z)
(minimize z :lower ((_ to_fp 2 5) RNE 2)           :upper ((_ to_fp 2 5) RNE 2)    :id unsat_2_z)

;
; ERROR #1: non-constant value
;
(declare-fun some_var () Int)
(minimize x :lower some_var)
(minimize y :lower ((_ to_bv 4) some_var))

;
; ERROR #2: incorrect type
;
(minimize x :lower bv_bound)
(minimize x :lower fp_bound)
(minimize y :lower int_bound)
(minimize y :lower real_bound)
(minimize y :lower fp_bound)
(minimize y :lower ((_ to_bv 8) 4))
(minimize z :lower int_bound)
(minimize z :lower real_bound)
(minimize z :lower bv_bound)
(minimize z :lower (_ +zero 8 24))

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)
