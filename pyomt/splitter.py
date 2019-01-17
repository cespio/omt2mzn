#Francesco Contaldo attempt
from six.moves import cStringIO

import pyomt.operators as op
from pyomt.walkers import TreeWalker
from pyomt.walkers.generic import handles
from pyomt.utils import quote
from pyomt.constants import is_pyomt_fraction, is_pyomt_integer
from pyomt.shortcuts import get_formula_size
from pyomt.substituter import Substituter


class Splitter(TreeWalker):

    def __init__(self, env=None):
        TreeWalker.__init__(self, env=env)
        self.node_var=[]
        Substituter.__init__(self,env=env)

    def splitter(self, f, threshold=None):
        self.walk(f, threshold=None) #optimathsat
        list_id=[n.node_id() for n in self.node_var]
        #Substituter.substitute(f,)

    def walk_threshold(self, formula):
        pass

    def walk_nary(self, formula):
        args = formula.args()
        for s in args[:-1]:
            yield s
        yield args[-1]

    def walk_split(self,formula):
        print("OR/AND ")
        args = formula.args()
        print (get_formula_size(args[0]))
        if get_formula_size(args[0])>=200: ##sono boolean
            self.node_var.append(args[0])
        else:
            yield args[0]
        print(get_formula_size(args[1]))
        if get_formula_size(args[1])>=200:
            self.node_var.append(args[1])
        else:
            yield args[1]
        #for s in args[:-1]:
        #    yield s
        #yield args[-1]

    def walk_quantifier(self, op_symbol, var_sep, sep, formula):
        if len(formula.quantifier_vars()) > 0:
            for s in formula.quantifier_vars()[:-1]:
                yield s
            yield formula.quantifier_vars()[-1]
            yield formula.arg(0)
        else:
            yield formula.arg(0)

    def walk_not(self, formula):
        yield formula.arg(0)

    def walk_symbol(self, formula):
        pass

    def walk_function(self, formula):
        yield formula.function_name()
        for p in formula.args()[:-1]:
            yield p
        yield formula.args()[-1]

    def walk_real_constant(self, formula):
        assert is_pyomt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        # TODO: Remove this once issue 113 in gmpy2 is solved
        v = formula.constant_value()
        n,d = v.numerator, v.denominator

    def walk_int_constant(self, formula):
        assert is_pyomt_integer(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))


    def walk_bool_constant(self, formula):
        pass

    def walk_bv_constant(self, formula):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.write("(_ bv%d %d)" % (formula.bv_width(),
        #                             formula.constant_value()))
        pass

    def walk_algebraic_constant(self, formula):
        pass

    def walk_bv_extract(self, formula):
        yield formula.arg(0)


    def walk_bv_neg(self, formula):
        yield formula.arg(0)


    def walk_bv_ror(self, formula):
        yield formula.arg(0)

    def walk_bv_rol(self, formula):
        yield formula.arg(0)

    def walk_bv_zext(self, formula):
        yield formula.arg(0)

    def walk_bv_sext(self, formula):
        yield formula.arg(0)

    def walk_ite(self, formula):
        yield formula.arg(0)
        yield formula.arg(1)
        yield formula.arg(2)

    def walk_forall(self, formula):
        return self.walk_quantifier("forall ", ", ", " . ", formula)

    def walk_exists(self, formula):
        return self.walk_quantifier("exists ", ", ", " . ", formula)

    def walk_toreal(self, formula):
        yield formula.arg(0)

    def walk_str_constant(self, formula):
        assert (type(formula.constant_value()) == str ), \
            "The type was " + str(type(formula.constant_value()))

    def walk_str_length(self,formula):
        self.walk(formula.arg(0))

    def walk_str_charat(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))

    def walk_str_concat(self,formula, **kwargs):
        for arg in formula.args()[:-1]:
            self.walk(arg)
        self.walk(formula.args()[-1])

    def walk_str_contains(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))

    def walk_str_indexof(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))
        self.walk(formula.arg(2))

    def walk_str_replace(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))
        self.walk(formula.arg(2))

    def walk_str_substr(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))
        self.walk(formula.arg(2))

    def walk_str_prefixof(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))

    def walk_str_suffixof(self,formula, **kwargs):
        self.walk(formula.arg(0))
        self.walk(formula.arg(1))

    def walk_str_to_int(self,formula, **kwargs):
        self.walk(formula.arg(0))

    def walk_int_to_str(self,formula, **kwargs):
        self.walk(formula.arg(0))

    def walk_array_select(self, formula):
        yield formula.arg(0)
        yield formula.arg(1)

    def walk_array_store(self, formula):
        yield formula.arg(0)
        yield formula.arg(1)
        yield formula.arg(2)

    def walk_array_value(self, formula):
        yield formula.array_value_default()
        assign = formula.array_value_assigned_values_map()
        # We sort the array value assigments in lexicographic order
        # for deterministic printing
        for k in sorted(assign, key=str):
            yield k
            yield assign[k]


    def walk_bv_tonatural(self, formula):
        yield formula.arg(0)

    def walk_and(self, formula): return self.walk_split(formula)
    def walk_or(self, formula): return self.walk_split(formula)
    def walk_plus(self, formula): return self.walk_nary(formula)
    def walk_times(self, formula): return self.walk_nary(formula)
    def walk_div(self, formula): return self.walk_nary(formula)
    def walk_pow(self, formula): return self.walk_nary(formula)
    def walk_iff(self, formula): return self.walk_nary(formula)
    def walk_implies(self, formula): return self.walk_nary(formula)
    def walk_minus(self, formula): return self.walk_nary(formula)
    def walk_equals(self, formula): return self.walk_nary(formula)
    def walk_le(self, formula): return self.walk_nary(formula)
    def walk_lt(self, formula): return self.walk_nary(formula)
    def walk_bv_xor(self, formula): return self.walk_nary(formula)
    def walk_bv_concat(self, formula): return self.walk_nary(formula)
    def walk_bv_udiv(self, formula): return self.walk_nary(formula)
    def walk_bv_urem(self, formula): return self.walk_nary(formula)
    def walk_bv_sdiv(self, formula): return self.walk_nary(formula)
    def walk_bv_srem(self, formula): return self.walk_nary(formula)
    def walk_bv_sle(self, formula): return self.walk_nary(formula)
    def walk_bv_slt(self, formula): return self.walk_nary(formula)
    def walk_bv_ule(self, formula): return self.walk_nary(formula)
    def walk_bv_ult(self, formula): return self.walk_nary(formula)
    def walk_bv_lshl(self, formula): return self.walk_nary(formula)
    def walk_bv_lshr(self, formula): return self.walk_nary(formula)
    def walk_bv_ashr(self, formula): return self.walk_nary(formula)
    def walk_bv_comp(self, formula): return self.walk_nary(formula)
    walk_bv_and = walk_and
    walk_bv_or = walk_or
    walk_bv_not = walk_not
    walk_bv_add = walk_plus
    walk_bv_mul = walk_times
    walk_bv_sub = walk_minus