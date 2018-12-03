#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import re
import copy
import collections
import shortcuts as sh
from six.moves import cStringIO
import pyomt.operators as op
from pyomt.walkers import TreeWalker,DagWalker
from pyomt.walkers.generic import handles
from pyomt.utils import quote
from pyomt.environment import get_env
from pyomt.constants import is_pyomt_fraction, is_pyomt_integer
from pyomt.oracles import SizeOracle
from pyomt.typing import BOOL, REAL, INT, BVType, ArrayType, STRING


'''
#TODO: -> bveq con = in print con daggify
'''


class TreeMznPrinter(TreeWalker):
    """Performs serialization of a formula in a human-readable way.

    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x * y) -> z'
    """

    def __init__(self,max_int_bit_size,stream,env=None):
        TreeWalker.__init__(self, env=env)
        self.stream = stream
        self.write = self.stream.write
        self.name_seed = 0
        self.template = "bv_%d"
        self.max_int_bit_size=max_int_bit_size
        
    

    def printer(self, f,threshold=None):
        """Performs the serialization of 'f' MZN"""
        self.walk(f,threshold=None)
                
    def _new_symbol_bv(self):
        res = (self.template % self.name_seed)
        self.name_seed += 1
        return res


    def walk_threshold(self, formula):
        self.write("...")

    def walk_nary(self, formula, operator):
        args = formula.args()
        if operator=="ite":
            self.write(" if ")
            yield args[0]
            self.write(" then ")
            yield args[1]
            self.write(" else ")
            yield args[2]
            self.write(" endif ")
        elif len(args)==1 and (operator=="not" or operator=="int2float"):
            self.write(" not (")
            yield args[0]
            self.write(")")
        else:
            self.write("(")
            yield args[0]
            for s in args[1:]:
                self.write(" ")
                self.write(operator)
                self.write(" ")
                yield s
            self.write(")")
    
    def walk_div(self, formula):    
        typeF=str(formula.get_type()).lower().replace("real","float")
        if typeF=="float":
            return self.walk_nary(formula,"/")
        else:
            return self.walk_nary(formula,"div")

    def walk_pow(self, formula):    
        args = formula.args()
        self.write("pow(")
        yield args[0]
        self.write(",")
        yield args[1]
        self.write(")")

    def walk_not(self, formula):    return self.walk_nary(formula,"not")
    def walk_and(self, formula):    return self.walk_nary(formula, "/\\")
    def walk_or(self, formula):     return self.walk_nary(formula, "\/")
    def walk_plus(self, formula):   return self.walk_nary(formula, "+")
    def walk_times(self, formula):  return self.walk_nary(formula, "*")
    def walk_iff(self, formula):    return self.walk_nary(formula, "<->")
    def walk_implies(self, formula):return self.walk_nary(formula, "->")
    def walk_minus(self, formula):  return self.walk_nary(formula, "-")
    def walk_equals(self, formula): return self.walk_nary(formula, "=") 
    def walk_le(self, formula):     return self.walk_nary(formula, "<=")
    def walk_lt(self, formula):     return self.walk_nary(formula, "<")
    def walk_toreal(self, formula): return self.walk_nary(formula, "int2float")
    def walk_ite(self, formula):    return self.walk_nary(formula, "ite")

    ### ----------------- BV ------------------------------------------#
    
    def walk_bv_and(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (((( """%(sym))
        yield args[0] 
        self.write("div pow(2,i)) mod 2)) * (((")
        yield args[1] 
        self.write("""div pow(2,i)) mod 2))) | i in 0..%s]);
                         in %s\n""" %(size-1,sym))

    def walk_bv_or(self,formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int : %s  = sum([pow(2,i)* ((((("""%(sym))
        yield args[0] 
        self.write("div pow(2,i)) mod 2)) + (((")
        yield args[1]
        self.write("""div pow(2,i)) mod 2)))>0) | i in 0..%s]);
                       } in %s\n""" %(size-1,sym))

    def walk_bv_not(self,formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (1-("""%(sym))
        yield args[0]
        self.write("""div pow(2,i)) mod 2) | i in 0..%s]);
                       } in %s\n""" %(size-1,sym))

    def walk_bv_xor(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int : %s  = sum([pow(2,i)* ((((("""%(sym))
        yield args[0]
        self.write("div pow(2,i)) mod 2)) != (((")
        yield args[1] 
        self.write("""div pow(2,i)) mod 2)))) | i in 0..%s]);
                       } in %s\n""" %(size-1,sym))
        
    def walk_bv_add(self,formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write("""let{ var int:%s = ("""%(sym))
        yield args[0]
        self.write(" + ") 
        yield args[1]
        self.write(""") mod %s;
                        } in sym\n"""%(str(pow(2,size)),sym))
    

    def walk_bv_sub(self,formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(";\n var int:%s_args2_in = "%(sym))
        yield args[1]
        self.write(""";\nvar int:%s_args1 = if %s_args1_in >= %s then %s_args1_in-%s else %s_args1_in endif;
                    var int:%s_args2 = if %s_args2_in >= %s then %s_args2_in-%s else %s_args2_in endif;
                    var int:%s_ris = (%s_args1 - %s_args2) mod %s;
                    var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                } in %s\n""" %(sym,args[0],str(pow(2,size-1)),sym,pow(2,size),sym,
                            sym,args[1],str(pow(2,size-1)),sym,pow(2,size),sym,
                            sym,sym,sym,str(pow(2,size)),
                            sym,sym,sym,str(pow(2,size)),sym,sym))


    def walk_bv_neg(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let {
                            var int:%s_args1_in = """)
        yield args[0];
        self.write(""";\var int:%s_args1 = if %s_args1_in >= %s then %s_args1_in-%s else %s_args1_in endif;
                            var int:%s_ris = (0 - %s_args1);
                            var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in %s\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym,sym))

    def walk_bv_mul(self,formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int:%s = ( """%(sym))
        yield args[0]
        self.write(" * ")
        yield args[1]
        self.write(""") mod %s
                        } in %s\n"""%(str(pow(2,size)),sym))

    def walk_bv_concat(self, formula):
        sym = self._new_symbol_bv()
        args = formula.args()
        size_s1=formula.args()[0].bv_width()
        size_s2=formula.args()[1].bv_width()
        self.write(""" let { var int: %s = """%(sym))
        yield args[1]
        self.write(" + sum([pow(2,i+%s)*((("%(size_s2))
        yield args[0]
        self.write(""" div pow(2,i)) mod 2)) | i in 0..%s]);
                            } in %s\n"""%(size_s1-1,sym))

    def walk_bv_udiv(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int:%s = ("""%(sym))
        yield args[0]
        self.write(" div ")
        yield args[1]
        self.write(""") } in %s\n"""%(sym))

    def walk_bv_urem(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int:%s = (""" %(sym))
        yield args[0]
        self.write(" mod ")
        yield args[1]
        self.write(""") } in %s\n"""%(sym))

    def walk_bv_sdiv(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { 
                             var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(""";\nvar int:%s_args2_in = """%(sym))
        yield args[1]                    
        self.write("""    ;\nvar int:%s_args1 = if %s_args1_in >= %s then %s_args1_in-%s else %s_args1_in endif;
                             var int:%s_args2 = if %s_args2_in >= %s then %s_args2_in-%s else %s_args2_in endif;
                             var int:%s_ris = (%s_args1 div %s_args2);  
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n %s""" %(sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym,sym))

    def walk_bv_srem(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(";\n var int:%s_args2_in = "%(sym))
        yield args[1]
        self.write(""";\nvar int:%s_args1 = if %s_args1_in >= %s then %s_args1_in-%s else %s_args1_in endif;
                             var int:%s_args2 = if %s_args2_in >= %s then %s_args2_in-%s else %s_args2_in endif;
                             var int:%s_ris = (%s_args1 mod %s_args2);
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in %s\n""" %(sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym,sym))

    def walk_bv_sle(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(";\n var int:%s_args2_in = "%(sym))
        yield args[1]
        self.write(""";\nvar int:%s_args1 = if %s_args1_in >= %s then %s_args1_in-%s else %s_args1_in endif;
                             var int:%s_args2 = if %s_args2_in >= %s then %s_args2_in-%s else %s_args2_in endif;
                             var bool:%s = (%s_args1 <= %s_args2)  
                        } in %s\n"""%(sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,str(pow(2,size-1)),args[1],str(pow(2,size)),sym,
                                   sym,sym,sym,sym))

    def walk_bv_slt(self, formula):  
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(";\n var int:%s_args2_in = "%(sym))
        yield args[1]
        self.write(""";\nvar int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var bool:%s = (%s_args1 < %s_args2)  
                        } in  %s\n"""%(sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),sym,
                                   sym,sym,sym,sym))

    def walk_bv_ule(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var bool:%s  = (""" %(sym))
        yield args[0]
        self.write(" <= ")
        yield args[1]
        self.write(")} in %s\n"%(sym))


    def walk_bv_ult(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var bool:%s  = (""" %(sym))
        yield args[0]
        self.write(" <= ")
        yield args[1]
        self.write(")} in %s\n"%(sym))
        
    def walk_bv_lshl(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int:%s = ("""%(sym))
        yield args[0]
        self.write("* pow(2,")
        yield args[1]
        self.write(""")) mod %s; } in %s\n"""%(str(pow(2,size)),sym))

    def walk_bv_lshr(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int:%s = ("""%(sym))
        yield args[0]
        self.write(""" div pow(2,""")
        yield args[1]
        self.write(""" ))) } in %s\n"""%(sym))
    

    def walk_bv_ashr(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(";\n var int:%s_args2_in = "%(sym))
        yield args[1]
        self.write(""";\nvar int:%s_args1 = if %s_args1_in>=%s then %s_args1_in-%s+%s else %s_args1_in endif;
                              var int:%s_ris =  %s_args1 div pow(2,%s_args2_in);
                              var int:%s = if %s_args1_in<%s  then %s_ris else sum([pow(2,i)*(((%s_ris+%s) div pow(2,i)) mod 2)|i in 0..%s]) endif;
                            } in %s\n"""%(sym,sym,str(pow(2,size-1)),sym,str(pow(2,size)),str(pow(2,self.max_int_bit_size-1)),sym, 
                                      sym,sym,sym,
                                      sym,args,sym,str(pow(2,size-1)),sym,sym,str(pow(2,self.max_int_bit_size-3)+pow(2,self.max_int_bit_size-2)+pow(2,self.max_int_bit_size-1)+pow(2,size)),size-1,sym))

    def walk_bv_comp(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        self.write(""" let { var int : %s  = if """%(sym))
        yield args[0]
        self.write(" = ")
        yield args[1]
        self.write(""" then 1 else 0 endif; } in %s\n""" %(sym))
    
    def walk_bv_tonatural(self, formula):
        yield formula.args()[0]
    
    def walk_bv_extract(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        start=int(formula.bv_extract_start())
        end=int(formula.bv_extract_end())
        if start != end:
            self.write(""" let { var int : %s_s1 = """ %(sym))
            yield args[0] 
            self.write("""div %s;
                            var int : %s = sum([pow(2,i)*(((%s_s1 div pow(2,i)) mod 2)) | i in 0..%s])
                        } in %s\n"""%(str(pow(2,start)),sym,sym,str(end-start),sym))
                                

        else:
            self.write(""" let { var int : %s =  ("""%(sym))
            yield args[0]
            self.write(""" div pow(2,%s)) mod 2; } in %s\n""" %(start,sym))
    
    def walk_bv_ror(self, formula): 
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        rotate=formula.bv_rotation_step()%size
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(""";\nvar int:%s = (%s_args1_in div %s + ((%s_args1_in * %s) mod %s)) mod %s;
                            } in %s\n"""%(sym,sym,str(pow(2,rotate)),sym,str(pow(2,size-rotate)),str(pow(2,size)),str(pow(2,size)),sym))
    
    def walk_bv_rol(self, formula):
        sym = self._new_symbol_bv()
        size = formula.bv_width()
        args = formula.args()
        rotate=formula.bv_rotation_step()%size
        self.write(""" let { 
                    var int:%s_args1_in = """%(sym))
        yield args[0]
        self.write(""";\nvar int:%s = (%s_args1_in div %s) + ((%s_args1_in * %s mod %s)) mod %s; 
                           } in %s\n"""%(sym,str(pow(2,size-rotate)),sym,str(pow(2,rotate)),str(pow(2,size)),str(pow(2,size),sym)))

    def walk_bv_zext(self, formula): 
        yield formula.args()[0]

    def walk_bv_sext(self, formula):
        sym = self._new_symbol_bv()
        args = formula.args()
        self.write(""" let { var int:%s = """%(sym))
        yield args[0]
        self.write("""+sum([pow(2,i) | i in %s..%s ]); } in %s\n"""%(formula.args()[0].bv_width(),formula.bv_width()-1,sym))

    
    

    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name()))

    def walk_quantifier(self, op_symbol, var_sep, sep, formula):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    
    def walk_function(self, formula):
        yield formula.function_name()
        self.write("(")
        for p in formula.args()[:-1]:
            yield p
            self.write(", ")
        yield formula.args()[-1]
        self.write(")")

    def walk_real_constant(self, formula):
        assert is_pyomt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        # TODO: Remove this once issue 113 in gmpy2 is solved
        v = formula.constant_value()
        n,d = v.numerator, v.denominator
        if formula.constant_value().denominator == 1:
            self.write("%s.0" % n)
        else:
            self.write("%s/%s" % (n, d))

    def walk_int_constant(self, formula):
        assert is_pyomt_integer(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        self.write(str(formula.constant_value()))

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("true")
        else:
            self.write("false")

    def walk_bv_constant(self, formula): 
        self.write(str(formula.constant_value()))

    def walk_algebraic_constant(self, formula):
        self.write(str(formula.constant_value()))     
    
    
    def walk_forall(self, formula):
        #return self.walk_quantifier("forall ", ", ", " . ", formula)
        raise NotImplementedErr("The forall operator cannot be translated into Mzn")

    def walk_exists(self, formula):
        #return self.walk_quantifier("exists ", ", ", " . ", formula)
        raise NotImplementedErr("The exists operator cannot be translated into Mzn")

    

    def walk_str_constant(self, formula):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_length(self,formula):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_charat(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_concat(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_contains(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_indexof(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_replace(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_substr(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_prefixof(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_suffixof(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_to_int(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_int_to_str(self,formula, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_array_select(self, formula):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_array_store(self, formula):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_array_value(self, formula):
        raise NotImplementedErr("Operation that cannot be translated into MzN")


#EOC HRPrinter


class DagMznPrinter(DagWalker):
    
    def __init__(self,max_int_bit_size,stream,template="tmp_%d"):
        DagWalker.__init__(self, invalidate_memoization=True)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = 0
        self.template = template
        self.names = None
        self.mgr = get_env().formula_manager
        self.max_int_bit_size=max_int_bit_size

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We invoke the relevant function (walk_exists or
            #    walk_forall) to print the formula
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=None, **kwargs)

            # 2. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            DagWalker._push_with_children_to_stack(self, formula, **kwargs)

    def printer(self, f):
        self.openings = 0
        self.name_seed = 0
        self.names = set(quote(x.symbol_name()) for x in f.get_free_variables())
        key = self.walk(f)
        self.write(key)
    


    def _new_symbol(self):
        while (self.template % self.name_seed) in self.names:
            self.name_seed += 1
        res = (self.template % self.name_seed)
        self.name_seed += 1
        return res

    def walk_nary(self, formula, args, operator):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        typeF=str(formula.get_type()).lower().replace("real","float")
        self.write(" let { var %s : %s = ( " % (typeF,sym))
        if operator=="ite":
            self.write(" if ")
            self.write(args[0])
            self.write(" then ")
            self.write(args[1])
            self.write(" else ")
            self.write(args[2])
            self.write(" endif ")
            self.write(" )} in \n")
        elif len(args)==1 and (operator=="not" or operator=="int2float"):
            self.write(" ")
            self.write(" not (")
            self.write(args[0])
            self.write(")")
            self.write(" )} in \n")
        else:
            self.write(args[0])
            for s in args[1:]:
                self.write(" ")
                self.write(operator)
                self.write(" ")
                self.write(s)
            self.write(" )} in \n")
            #self.write(");\n")
        return sym

    def walk_and(self, formula, args):
        return self.walk_nary(formula, args, "/\\")

    def walk_or(self, formula, args):
        return self.walk_nary(formula, args, "\/")

    def walk_not(self, formula, args):
        return self.walk_nary(formula, args, "not")

    def walk_implies(self, formula, args):
        return self.walk_nary(formula, args, "->")

    def walk_iff(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_plus(self, formula, args):
        return self.walk_nary(formula, args, "+")

    def walk_minus(self, formula, args):
        return self.walk_nary(formula, args, "-")

    def walk_times(self, formula, args):
        return self.walk_nary(formula, args, "*")

    def walk_equals(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_le(self, formula, args):
        return self.walk_nary(formula, args, "<=")

    def walk_lt(self, formula, args):
        return self.walk_nary(formula, args, "<")

    def walk_ite(self, formula, args):
        return self.walk_nary(formula, args, "ite")

    def walk_toreal(self, formula, args):
        return self.walk_nary(formula, args, "int2float")

    def walk_div(self, formula, args):
        typeF=str(formula.get_type()).lower().replace("real","float")
        if typeF=="float":
            return self.walk_nary(formula, args, "/")
        else:
            return self.walk_nary(formula,args, "div")

    def walk_pow(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        typeF=str(formula.get_type()).lower().replace("real","float")
        self.write("""let { var %s:%s = pow(%s,%s)  
                      } in\n"""%(typeF,sym,args[0],args[1]))
        return sym


    def walk_bv_and(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1       
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* ((((%s div pow(2,i)) mod 2)) * (((%s div pow(2,i)) mod 2))) | i in 0..%s]);
                       } in\n""" %(sym,args[0],args[1],size-1))
        return sym

    def walk_bv_or(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1      
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (((((%s div pow(2,i)) mod 2)) + (((%s div pow(2,i)) mod 2)))>0) | i in 0..%s]);
                       } in\n""" %(sym,args[0],args[1],size-1))
        return sym

    def walk_bv_not(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1      
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (1-(%s div pow(2,i)) mod 2) | i in 0..%s]);
                       } in\n""" %(sym,args[0],size-1))
        return sym

    def walk_bv_xor(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1      
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (((((%s div pow(2,i)) mod 2)) != (((%s div pow(2,i)) mod 2)))) | i in 0..%s]);
                       } in\n""" %(sym,args[0],args[1],size-1))
        return sym 

    def walk_bv_add(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1       
        size=formula.bv_width()  
        self.write("""let{ var int:%s = (%s+%s) mod %s;
                        } in\n"""%(sym,args[0],args[1],pow(2,size)))
        return sym

    def walk_bv_sub(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1       
        size=formula.bv_width()   
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                            var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                            var int:%s_ris = (%s_args1 - %s_args2) mod %s;
                            var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                       } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],pow(2,size),args[0],
                                  sym,args[1],str(pow(2,size-1)),args[1],pow(2,size),args[1],
                                  sym,sym,sym,str(pow(2,size)),
                                  sym,sym,sym,str(pow(2,size)),sym))
        return sym

    def walk_bv_neg(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1   
        size=formula.bv_width()   
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                            var int:%s_ris = (0 - %s_args1);
                            var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym))
        return sym


    def walk_bv_mul(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        typeF=int(str(formula.get_type()).lower())       
        size=formula.bv_width()    
        self.write(""" let { var int:%s = (%s*%s) mod %s
                        } in\n"""%(sym,args[0],args[1],str(pow(2,size))))
        return sym

            

    def walk_bv_udiv(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1     
        self.write(""" let { var int:%s = (%s div %s)  
                       } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_urem(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1  
        self.write(""" let { var int:%s = (%s mod %s)  
                        } in\n"""%(sym,args[0],args[1]))
        return sym


    def walk_bv_lshl(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        typeF=str(formula.get_type()).lower()       
        size=re.sub(r"bv{([0-9]+)}",r"\1",typeF)    
        self.write(""" let { var int:%s = (%s*pow(2,%s)) mod %s;
                        } in\n"""%(sym,args[0],args[1],str(pow(2,size))))
        return sym


    def walk_bv_lshr(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1        
        self.write(""" let { var int:%s = (%s div pow(2,%s))
                        } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_ult(self, formula, args):    #depend on the encoding
        sym = self._new_symbol()
        self.openings += 1
        self.write(""" let { var bool:%s = (%s<%s) 
                        } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_ule(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        self.write(""" let { var bool:%s = (%s<=%s)
                       } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_slt(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        size=int(formula.args()[0].bv_width())  
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var bool:%s = (%s_args1 < %s_args2)  
                        } in  """%(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym))
        return sym

    def walk_bv_sle(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        size=int(formula.args()[0].bv_width())  
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var bool:%s = (%s_args1 <= %s_args2)  
                        } in  """%(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym))
        return sym

    def walk_bv_concat(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1
        size_s1=formula.args()[0].bv_width()
        size_s2=formula.args()[1].bv_width()
        self.write(""" let { var int: %s = %s + sum([pow(2,i+%s)*(((%s div pow(2,i)) mod 2)) | i in 0..%s]);
                            } in\n"""%(sym,args[1],size_s2,args[0],size_s1-1))
        return sym

    def walk_bv_comp(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1   
        self.write(""" let { var int : %s  = if %s=%s then 1 else 0 endif;
                        } in\n""" %(sym,args[0],args[1]))
        return sym


    def walk_bv_ashr(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1    
        size=formula.bv_width() 
        self.write(""" let {  var int:%s_args1 = if %s>=%s then %s-%s+%s else %s endif;
                              var int:%s_ris =  %s_args1 div pow(2,%s);
                              var int:%s = if %s<%s  then %s_ris else sum([pow(2,i)*(((%s_ris+%s) div pow(2,i)) mod 2)|i in 0..%s]) endif;
                            } in\n"""%(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),str(pow(2,self.max_int_bit_size-1)),args[0], 
                                      sym,sym,args[1],
                                      sym,args[0],str(pow(2,size-1)),sym,sym,str(pow(2,self.max_int_bit_size-3)+pow(2,self.max_int_bit_size-2)+pow(2,self.max_int_bit_size-1)+pow(2,size)),size-1))
        return sym


    def walk_bv_sdiv(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1       
        size=formula.bv_width()   
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_ris = (%s_args1 div %s_args2);  
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym))
        return sym

    def walk_bv_srem(self, formula, args):
        sym = self._new_symbol()
        self.openings += 1       
        size=formula.bv_width()  #(sign follows dividend)
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_ris = (%s_args1 mod %s_args2);
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym))
        return sym


    def walk_bv_tonatural(self, formula, args):
        # Kind of useless
        #return self.walk_nary(formula, args, "bv2nat")
        sym = self._new_symbol()
        self.openings += 1
        self.write(""" let { var int:%s = %s;  
                        } in\n"""%(sym,args[0]))
        return sym

    def walk_array_select(self, formula, args):
        return self.walk_nary(formula, args, "select")

    def walk_array_store(self, formula, args):
        return self.walk_nary(formula, args, "store")

    def walk_symbol(self, formula, **kwargs):
        return quote(formula.symbol_name())

    def walk_function(self, formula, args, **kwargs):
        return self.walk_nary(formula, args, formula.function_name())

    def walk_int_constant(self, formula, **kwargs):
        #print "INT CONSTANTANT ",formula.constant_value()
        if formula.constant_value() < 0:
            return "(- " + str(-formula.constant_value()) + ")"
        else:
            return str(formula.constant_value())

    def walk_real_constant(self, formula, **kwargs):
        #print "REAL CONSTANTANT ",formula.constant_value()
        #print "SIMPLY ",formula.constant_value.
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            return template % ( "(" + str(n) + ".0 / " + str(d) + ".0)" )
        else:
            return template % (str(n) + ".0")

    def walk_bv_constant(self, formula, **kwargs):
        return str(formula.constant_value())
        #return "#b" + res


    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return "true"
        else:
            return "false"

    def walk_str_constant(self, formula, **kwargs):
        return '"' + formula.constant_value() + '"'

    def walk_forall(self, formula, args, **kwargs):
        #return self._walk_quantifier("forall", formula, args)
        raise NotImplementedErr("The forall operator cannot be translated into Mzn")

    def walk_exists(self, formula, args, **kwargs):
        #return self._walk_quantifier("exists", formula, args)
        raise NotImplementedErr("The exists operator cannot be translated into Mzn")

    def _walk_quantifier(self, operator, formula, args):
        '''
        assert args is None
        assert len(formula.quantifier_vars()) > 0
        sym = self._new_symbol()
        self.openings += 1

        self.write("(let ((%s (%s (" % (sym, operator))

        for s in formula.quantifier_vars():
            self.write("(")
            self.write(quote(s.symbol_name()))
            self.write(" %s)" % s.symbol_type().as_smtlib(False))
        self.write(") ")

        subprinter = SmtDagPrinter(self.stream,0,0) #Da rivedere
        subprinter.printer(formula.arg(0))

        self.write(")))")
        return sym
        '''
        raise NotImplementedErr("The quantifier cannot be translated into Mzn")

    def walk_bv_extract(self, formula, args, **kwargs):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        start=int(formula.bv_extract_start())
        end=int(formula.bv_extract_end())
        if start != end:
            self.write(""" let { var int : %s_s1 = %s div %s;
                                 var int : %s = sum([pow(2,i)*(((%s_s1 div pow(2,i)) mod 2)) | i in 0..%s])
                            } in\n"""%(sym,args[0],str(pow(2,start)),sym,sym,str(end-start)))
                                

        else:
            self.write(""" let { var int : %s =  (%s div pow(2,%s)) mod 2;
                            } in\n""" %(sym,args[0],start))
        return sym

    @handles(op.BV_SEXT, op.BV_ZEXT)
    def walk_bv_extend(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        sym = self._new_symbol()
        self.openings += 1
        if formula.is_bv_zext():
            self.write(""" let { var int:%s = %s;  
                          } in\n"""%(sym,args[0]))
        else:
            assert formula.is_bv_sext() 
            self.write(""" let { var int:%s = %s+sum([pow(2,i) | i in %s..%s ]);  
                           } in\n"""%(sym,args[0],formula.args()[0].bv_width(),formula.bv_width()-1))
        return sym

    @handles(op.BV_ROR, op.BV_ROL)
    def walk_bv_rotate(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        sym = self._new_symbol()
        self.openings += 1
        size=formula.bv_width()
        rotate=formula.bv_rotation_step()%size
        if formula.is_bv_ror():
            self.write(""" let { var int:%s = (%s div %s + ((%s * %s) mod %s)) mod %s;
                            } in\n"""%(sym,args[0],str(pow(2,rotate)),args[0],str(pow(2,size-rotate)),str(pow(2,size)),str(pow(2,size))))
        else:
            self.write(""" let { var int:%s = (%s div %s) + ((%s * %s mod %s)) mod %s; 
                           } in\n"""%(sym,args[0],str(pow(2,size-rotate)),args[0],str(pow(2,rotate)),str(pow(2,size)),str(pow(2,size))))
        
        return sym

    def walk_str_length(self, formula, args, **kwargs):
        #return "(str.len %s)" % args[0])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_charat(self,formula, args,**kwargs):
        #return "( str.at %s %s )" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_concat(self, formula, args, **kwargs):
        '''
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "str.++ " ))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym
        '''
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_contains(self,formula, args, **kwargs):
        #return "( str.contains %s %s)" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_indexof(self,formula, args, **kwargs):
        #return "( str.indexof %s %s %s )" % (args[0], args[1], args[2])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_replace(self,formula, args, **kwargs):
        #return "( str.replace %s %s %s )" % (args[0], args[1], args[2])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_substr(self,formula, args,**kwargs):
        #return "( str.substr %s %s %s)" % (args[0], args[1], args[2])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_prefixof(self,formula, args,**kwargs):
        #return "( str.prefixof %s %s )" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_suffixof(self,formula, args, **kwargs):
        #return "( str.suffixof %s %s )" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_to_int(self,formula, args, **kwargs):
        #return "( str.to.int %s )" % args[0]
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_int_to_str(self,formula, args, **kwargs):
        #return "( int.to.str %s )" % args[0]
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_array_value(self, formula, args, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

class DagFathersMznPrinter(DagWalker):
    def __init__(self,max_int_bit_size,stream,dict_fathers,template="tmp_%d",boolean_invalidate=True):
        DagWalker.__init__(self, invalidate_memoization=boolean_invalidate)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = 0
        self.memoization = copy.copy(dict_fathers)
        self.template = template
        self.names = None
        self.mgr = get_env().formula_manager
        self.max_int_bit_size=max_int_bit_size
    

    ### MODIFIY THE DAGWALKER:
    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""
        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We invoke the relevant function (walk_exists or
            #    walk_forall) to print the formula
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=None, **kwargs)

            # 2. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            self.stack.append((True, formula))
            for s in self._get_children(formula):
                # Add only if not memoized already
                key = self._get_key(s, **kwargs)
                if key not in self.memoization or self.memoization[key]=="":
                    self.stack.append((False, s))

    def _compute_node_result(self, formula, **kwargs):
        """Apply function to the node and memoize the result.

        Note: This function assumes that the results for the children
              are already available.
        """
        key = self._get_key(formula, **kwargs)
        if key not in self.memoization or self.memoization[key]=="":
            try:
                f = self.functions[formula.node_type()]
            except KeyError:
                f = self.walk_error
            args = [self.memoization[self._get_key(s, **kwargs)] \
                    for s in self._get_children(formula)]
            self.memoization[key] = f(formula, args=args, **kwargs)
        else:
            pass

    def walk(self, formula, **kwargs):
        if formula in self.memoization and self.memoization[formula]!="":
            return self.memoization[formula]

        res = self.iter_walk(formula, **kwargs)

        if self.invalidate_memoization:
            self.memoization.clear()
        return res


    def printer(self, f):
        self.openings = 0
        self.name_seed = 0
        self.names = set(quote(x.symbol_name()) for x in f.get_free_variables())
        #print "formula",f,"con mem",self.memoization,"buffer",self.stream.getvalue()
        key = self.walk(f)
        self.write(key)
        
    
    def _new_symbol_bv(self,bv_template):
        while (bv_template % self.name_seed) in self.names:
            self.name_seed += 1
        res = (bv_template % self.name_seed)
        self.name_seed += 1
        return res
    

    def walk_nary(self, formula, args, operator):
        assert formula is not None
        str_out = ""
        self.openings += 1
        if operator=="ite":
            str_out = str_out + " if "
            str_out=str_out+args[0]
            str_out = str_out + " then " 
            str_out=str_out+args[1]
            str_out = str_out + " else "
            str_out=str_out+args[2]
            str_out = str_out + " endif "
        elif len(args)==1 and (operator=="not" or operator=="int2float"):
            str_out = str_out + "not ("
            str_out=str_out+args[0]
            str_out = str_out + ")"
        else:
            str_out = str_out + "("
            str_out=str_out+args[0]
            for s in args[1:]:
                str_out = str_out + " "
                str_out=str_out+operator
                str_out = str_out + " "
                str_out=str_out+s
            str_out = str_out + ")"
        return str_out

    def walk_and(self, formula, args):
        return self.walk_nary(formula, args, "/\\")

    def walk_or(self, formula, args):
        return self.walk_nary(formula, args, "\/")

    def walk_not(self, formula, args):
        return self.walk_nary(formula, args, "not")

    def walk_implies(self, formula, args):
        return self.walk_nary(formula, args, "->")

    def walk_iff(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_plus(self, formula, args):
        return self.walk_nary(formula, args, "+")

    def walk_minus(self, formula, args):
        return self.walk_nary(formula, args, "-")

    def walk_times(self, formula, args):
        return self.walk_nary(formula, args, "*")

    def walk_equals(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_le(self, formula, args):
        return self.walk_nary(formula, args, "<=")

    def walk_lt(self, formula, args):
        return self.walk_nary(formula, args, "<")

    def walk_ite(self, formula, args):
        return self.walk_nary(formula, args, "ite")

    def walk_toreal(self, formula, args):
        return self.walk_nary(formula, args, "int2float")

    def walk_div(self, formula, args):
        typeF=str(formula.get_type()).lower().replace("real","float")
        if typeF=="float":
            return self.walk_nary(formula, args, "/")
        else:
            return self.walk_nary(formula,args, "div")

    def walk_pow(self, formula, args):
        return """pow(%s,%s)"""%(args[0],args[1])


    def walk_bv_and(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1   
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* ((((%s div pow(2,i)) mod 2)) * (((%s div pow(2,i)) mod 2))) | i in 0..%s]);
                         in\n""" %(sym,args[0],args[1],size-1))
        return sym

    def walk_bv_or(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1     
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (((((%s div pow(2,i)) mod 2)) + (((%s div pow(2,i)) mod 2)))>0) | i in 0..%s]);
                       } in\n""" %(sym,args[0],args[1],size-1))
        return sym

    def walk_bv_not(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1   
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (1-(%s div pow(2,i)) mod 2) | i in 0..%s]);
                       } in\n""" %(sym,args[0],size-1))
        return sym

    def walk_bv_xor(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1     
        size=formula.bv_width()
        self.write(""" let { var int : %s  = sum([pow(2,i)* (((((%s div pow(2,i)) mod 2)) != (((%s div pow(2,i)) mod 2)))) | i in 0..%s]);
                       } in\n""" %(sym,args[0],args[1],size-1))
        return sym 

    def walk_bv_add(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1       
        size=formula.bv_width()  
        self.write("""let{ var int:%s = (%s+%s) mod %s;
                        } in\n"""%(sym,args[0],args[1],pow(2,size)))
        return sym

    def walk_bv_sub(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1       
        size=formula.bv_width()   
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                            var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                            var int:%s_ris = (%s_args1 - %s_args2) mod %s;
                            var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                       } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],pow(2,size),args[0],
                                  sym,args[1],str(pow(2,size-1)),args[1],pow(2,size),args[1],
                                  sym,sym,sym,str(pow(2,size)),
                                  sym,sym,sym,str(pow(2,size)),sym))
        return sym

    def walk_bv_neg(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1   
        size=formula.bv_width()   
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_ris = (0 - %s_args1);
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym))
        return sym


    def walk_bv_mul(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        typeF=int(str(formula.get_type()).lower())       
        size=re.sub(r"bv{([0-9]+)}",r"\1",typeF)    
        self.write(""" let { var int:%s = (%s*%s) mod %s
                        } in\n"""%(sym,args[0],args[1],str(pow(2,size))))
        return sym

            

    def walk_bv_udiv(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1     
        self.write(""" let { var int:%s = (%s div %s)  
                       } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_urem(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1  
        self.write(""" let { var int:%s = (%s mod %s)  
                        } in\n"""%(sym,args[0],args[1]))
        return sym


    def walk_bv_lshl(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        typeF=str(formula.get_type()).lower()       
        size=re.sub(r"bv{([0-9]+)}",r"\1",typeF)    
        self.write(""" let { var int:%s = (%s*pow(2,%s)) mod %s;
                        } in\n"""%(sym,args[0],args[1],str(pow(2,size))))
        return sym


    def walk_bv_lshr(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1        
        self.write(""" let { var int:%s = (%s div pow(2,%s))
                        } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_ult(self, formula, args):   
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        self.write(""" let { var bool:%s = (%s<%s) 
                        } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_ule(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        self.write(""" let { var bool:%s = (%s<=%s)
                       } in\n"""%(sym,args[0],args[1]))
        return sym

    def walk_bv_slt(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        size=int(formula.args()[0].bv_width())  
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var bool:%s = (%s_args1 < %s_args2)  
                        } in  """%(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym))
        return sym

    def walk_bv_sle(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        size=int(formula.args()[0].bv_width())  
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var bool:%s = (%s_args1 <= %s_args2)  
                        } in  """%(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym))
        return sym

    def walk_bv_concat(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        size_s1=formula.args()[0].bv_width()
        size_s2=formula.args()[1].bv_width()
        self.write(""" let { var int: %s = %s + sum([pow(2,i+%s)*(((%s div pow(2,i)) mod 2)) | i in 0..%s]);
                            } in\n"""%(sym,args[1],size_s2,args[0],size_s1-1))
        return sym

    def walk_bv_comp(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1   
        self.write(""" let { var int : %s  = if %s=%s then 1 else 0 endif;
                        } in\n""" %(sym,args[0],args[1]))
        return sym


    def walk_bv_ashr(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1    
        size=formula.bv_width() 
        self.write(""" let {  var int:%s_args1 = if %s>=%s then %s-%s+%s else %s endif;
                              var int:%s_ris =  %s_args1 div pow(2,%s);
                              var int:%s = if %s<%s  then %s_ris else sum([pow(2,i)*(((%s_ris+%s) div pow(2,i)) mod 2)|i in 0..%s]) endif;
                            } in\n"""%(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),str(pow(2,self.max_int_bit_size-1)),args[0], 
                                      sym,sym,args[1],
                                      sym,args[0],str(pow(2,size-1)),sym,sym,str(pow(2,self.max_int_bit_size-3)+pow(2,self.max_int_bit_size-2)+pow(2,self.max_int_bit_size-1)+pow(2,size)),size-1))
        return sym


    def walk_bv_sdiv(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1       
        size=formula.bv_width()   
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_ris = (%s_args1 div %s_args2);  
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym))
        return sym

    def walk_bv_srem(self, formula, args):
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1       
        size=formula.bv_width()  #(sign follows dividend)
        self.write(""" let { var int:%s_args1 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_args2 = if %s >= %s then %s-%s else %s endif;
                             var int:%s_ris = (%s_args1 mod %s_args2);
                             var int:%s = if %s_ris < 0 then %s_ris+%s else %s_ris endif;
                        } in\n""" %(sym,args[0],str(pow(2,size-1)),args[0],str(pow(2,size)),args[0],
                                   sym,args[1],str(pow(2,size-1)),args[1],str(pow(2,size)),args[1],
                                   sym,sym,sym,
                                   sym,sym,sym,str(pow(2,size)),sym))
        return sym


    def walk_bv_tonatural(self, formula, args):
        # Kind of useless
        #return self.walk_nary(formula, args, "bv2nat")
        return """%s"""% (args[0])

    def walk_array_select(self, formula, args):
        return self.walk_nary(formula, args, "select")

    def walk_array_store(self, formula, args):
        return self.walk_nary(formula, args, "store")

    def walk_symbol(self, formula, **kwargs):
        return quote(formula.symbol_name())

    def walk_function(self, formula, args, **kwargs):
        return self.walk_nary(formula, args, formula.function_name())

    def walk_int_constant(self, formula, **kwargs):
        #print "INT CONSTANTANT ",formula.constant_value()
        if formula.constant_value() < 0:
            return "(- " + str(-formula.constant_value()) + ")"
        else:
            return str(formula.constant_value())

    def walk_real_constant(self, formula, **kwargs):
        #print "REAL CONSTANTANT ",formula.constant_value()
        #print "SIMPLY ",formula.constant_value.
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            return template % ( "(" + str(n) + " / " + str(d) + ")" )
        else:
            return template % (str(n) + ".0")

    def walk_bv_constant(self, formula, **kwargs):
        return str(formula.constant_value())
        #return "#b" + res


    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return "true"
        else:
            return "false"

    def walk_str_constant(self, formula, **kwargs):
        return '"' + formula.constant_value() + '"'

    def walk_forall(self, formula, args, **kwargs):
        #return self._walk_quantifier("forall", formula, args)
        raise NotImplementedErr("The forall operator cannot be translated into Mzn")

    def walk_exists(self, formula, args, **kwargs):
        #return self._walk_quantifier("exists", formula, args)
        raise NotImplementedErr("The exists operator cannot be translated into Mzn")

    def _walk_quantifier(self, operator, formula, args):
        raise NotImplementedErr("The quantifier cannot be translated into Mzn")

    def walk_bv_extract(self, formula, args, **kwargs):
        assert formula is not None
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        start=int(formula.bv_extract_start())
        end=int(formula.bv_extract_end())
        if start != end:
            self.write(""" let { var int : %s_s1 = %s div %s;
                                 var int : %s = sum([pow(2,i)*(((%s_s1 div pow(2,i)) mod 2)) | i in 0..%s])
                            } in\n"""%(sym,args[0],str(pow(2,start)),sym,sym,str(end-start)))
                                

        else:
            self.write(""" let { var int : %s =  (%s div pow(2,%s)) mod 2;
                            } in\n""" %(sym,args[0],start))
        return sym
    @handles(op.BV_SEXT, op.BV_ZEXT)
    def walk_bv_extend(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        if formula.is_bv_zext():
            self.write(""" let { var int:%s = %s;  
                          } in\n"""%(sym,args[0]))
        else:
            assert formula.is_bv_sext() 
            self.write(""" let { var int:%s = %s+sum([pow(2,i) | i in %s..%s ]);  
                           } in\n"""%(sym,args[0],formula.args()[0].bv_width(),formula.bv_width()-1))
        return sym

    @handles(op.BV_ROR, op.BV_ROL)
    def walk_bv_rotate(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        sym=self._new_symbol_bv("bv_%d")
        self.openings += 1
        size=formula.bv_width()
        rotate=formula.bv_rotation_step()%size
        if formula.is_bv_ror():
            self.write(""" let { var int:%s = (%s div %s + ((%s * %s) mod %s)) mod %s;
                            } in\n"""%(sym,args[0],str(pow(2,rotate)),args[0],str(pow(2,size-rotate)),str(pow(2,size)),str(pow(2,size))))
        else:
            self.write(""" let { var int:%s = (%s div %s) + ((%s * %s mod %s)) mod %s; 
                           } in\n"""%(sym,args[0],str(pow(2,size-rotate)),args[0],str(pow(2,rotate)),str(pow(2,size)),str(pow(2,size))))
        
        return sym

    def walk_str_length(self, formula, args, **kwargs):
        #return "(str.len %s)" % args[0])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_charat(self,formula, args,**kwargs):
        #return "( str.at %s %s )" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_concat(self, formula, args, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_contains(self,formula, args, **kwargs):
        #return "( str.contains %s %s)" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_indexof(self,formula, args, **kwargs):
        #return "( str.indexof %s %s %s )" % (args[0], args[1], args[2])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_replace(self,formula, args, **kwargs):
        #return "( str.replace %s %s %s )" % (args[0], args[1], args[2])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_substr(self,formula, args,**kwargs):
        #return "( str.substr %s %s %s)" % (args[0], args[1], args[2])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_prefixof(self,formula, args,**kwargs):
        #return "( str.prefixof %s %s )" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_suffixof(self,formula, args, **kwargs):
        #return "( str.suffixof %s %s )" % (args[0], args[1])
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_str_to_int(self,formula, args, **kwargs):
        #return "( str.to.int %s )" % args[0]
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_int_to_str(self,formula, args, **kwargs):
        #return "( int.to.str %s )" % args[0]
        raise NotImplementedErr("Operation that cannot be translated into MzN")

    def walk_array_value(self, formula, args, **kwargs):
        raise NotImplementedErr("Operation that cannot be translated into MzN")


class MZNPrinter(object):
    """Return the MZN version of the input formula"""
    def __init__(self,printer_selection,max_int_bit_size,environment=None):
        self.environment = environment
        self.last_index=0
        self.max_int_bit_size=max_int_bit_size
        self.printer_selection=printer_selection #0 simple daggify, 1 2fathers labeling
        self.mgr = get_env()._formula_manager
    

    def get_fathers(self,formula):
        cnt = 0
        fathers = collections.OrderedDict()
        counter = collections.Counter()
        subs = {}
        q = [formula]
        while q:
            e = q.pop()
            for s in e.args():
                if s not in counter:
                    counter[s]=1
                else:
                    counter[s]+=1
                    if s not in fathers and len(s.args())>=2 and counter[s]>=2 :#and (("Bool" in str(s.get_type()) or "BV" in str(s.get_type()))):
                        ns = self.mgr._create_symbol("tmp_"+str(cnt),s.get_type())
                        subs[s]=ns
                        fathers[s]="tmp_"+str(cnt)
                        cnt+=1
                if counter[s]<2:
                    q.append(s)
        #print("counter",len(counter))
        #print("fathers",len(fathers))
        #print("subs",len(subs))
        return fathers,subs,formula

    def serialize(self,formula,daggify=True,output_file=None):
        if self.printer_selection==0:
            buf = cStringIO()
            if daggify:
                p = DagMznPrinter(self.max_int_bit_size,buf)
            else:
                p = TreeMznPrinter(self.max_int_bit_size,buf)
            p.printer(formula)
            res_f=buf.getvalue()
        else:
            #print "Inizio a costruire dict_f"
            dict_f,subs,formula = self.get_fathers(formula)
            buf = cStringIO()
            str_let=""
            str_let_list=[]            
            if dict_f:
                p = DagFathersMznPrinter(self.max_int_bit_size,buf,dict_f,boolean_invalidate=False)
                for sub_f in reversed(dict_f.keys()):
                    label=dict_f[sub_f]
                    p.stream=cStringIO()
                    p.memoization[sub_f]=""
                    p.write=p.stream.write
                    p.printer(sub_f)
                    str_let_list.append(" var %s : %s =  %s;  \n "%(str(sub_f.get_type()).lower().replace("real","float"),label,p.stream.getvalue()))
                    p.memoization[sub_f]=label
                    p.stream.close()
            buf = cStringIO()
            if dict_f:
                str_let_list.reverse()
                str_let_list.sort(key=lambda x:x.count("tmp"))
                str_let = "let {\n"+"".join(str_let_list)+"} in\n"
                formula=sh.substitute(formula,subs)
            #print("Inizio TreePrint")
            p = TreeMznPrinter(self.max_int_bit_size,buf)
            p.printer(formula)
            res=buf.getvalue()
            buf.close()

            res_f=str_let+"\n"+res
        if output_file is None:
            return res_f
        else:
            output_file.write("constraint ("+res_f+");\n")
        

#EOC MZNPrinter

class NotImplementedErr(StandardError):
    pass