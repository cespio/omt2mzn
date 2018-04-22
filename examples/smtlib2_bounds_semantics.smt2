; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; OBJECTIVE BOUNDS:
;     OptiMathSAT allows to specify optional lower and upper
;     bounds on each objective function. These bounds can be
;     used to run OptiMathSAT in binary/adaptive search mode.
;     Bounds interpretation:
;     - boxed/multi-independent optimization: each bound is
;       interpreted as local to the objective function on which
;       it is applied and it does not affect the search space of
;       any other objective;
;     - all other cases: bounds have a global scope and affect
;       the whole formula
;
;     Bounds can be specified by adding the following OPTIONAL
;     fields to any objective:
;
;         :lower <term>
;         :upper <term>
;
;     Note that <term> must have the same type of the objective
;     function and can only be a constant value. 
;     (for more details about bounds syntax,
;                       see: smtlib2_bounds_syntax.smt2)
;
; WARNING:
;     When minimizing, the lower bound is considered non-strict
;     whereas the upper bound is considered strict. Dual for
;     maximization.
;     When doing minmax, the lower bound is considered strict,
;     whereas the upper bound is considered non-strict. Dual for
;     maxmin.
;     Therefore, when the lower and upper bounds match, the
;     search interval is empty and the objective is unsat.
;
;     In order to run OptiMathSAT using the binary or adaptive
;     search strategies, the user must provide the non-strict
;     bound for the given objective. The strict bound can be
;     omitted, since it can be computed at run-time.
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
(declare-fun t () Real)

;
; GOALS
;
(minimize x)
(minimize y :lower (- 0.5) :upper (/ 1 2))
(minimize z :lower 0    :upper 1)
(minimize t :lower 0    :upper 0)
(maximize (+ y 1))

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)
