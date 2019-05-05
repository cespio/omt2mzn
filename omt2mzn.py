#!/usr/bin/env python
#   Copyright 2019 Franceso Contaldo
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

from pyomt.smtlib.parser import SmtLib20Parser
from pyomt.printers_mzn import MZNPrinter
from pyomt.environment import get_env
import argparse
import pyomt.typing as tp
import sys
import re
import os


class MultiTypeLexErr(StandardError):
    pass

class Omt2Mzn():
    #if flag bv = true bv array rap
    def __init__(self,file_in,file_out,flag_bigand,max_int_bit_size,printer_opt,asoft_var_type,float_domains):
        self.serializer=MZNPrinter(printer_opt,max_int_bit_size)
        self.input_file=file_in
        self.output_file=file_out
        self.flag_bigand=flag_bigand
        self.asoft_var_type=asoft_var_type
        self.float_domains=float_domains


    def startParsing(self):
        '''
            Function that call the SmtLib20Parser() to obtain the list of the commands
        '''
        parser = SmtLib20Parser()
        new_input_file = self.pre_proc_infile(self.input_file)
        script = parser.get_script_fname(new_input_file)
        commands = script.commands                   #getting the list of commands (set-option,set-logic,declaration,assert,command)
        self.parse_stack(commands,self.output_file)  #calling the main function
        os.remove(new_input_file)                    #removing the temporary file

    def pre_proc_infile(self,input_file):
        '''
            Creating a temporary file where to apply some syntax changes to the input file and introducing
            varialbes for the soft assertions
        '''
        lines=open(input_file).readlines()
        temp_file=open(input_file+"_temp","w")
        new_lines=[]                                        #new_lines
        set_declaration_id=set()                            #variable declarations for soft asserts, make sure they are unique
        for l in lines:
            if l[0]!=";" and not re.match(r"^%(.*)%$",l):   #skipping comments line
                l=re.sub(r";.*","",l)                       #deleting comments in the same line
                if "assert-soft" in l:
                    if ":id " in l:
                        new_var = l.split(":id")[-1].strip().replace(")","")
                    else:
                        new_var = "I"
                    if new_var not in set_declaration_id:
                        new_lines.append("\n;declaration of additional variable for assert-soft\n")
                        new_lines.append("\n(declare-fun "+new_var+" () %s)\n"%(self.asoft_var_type))
                        set_declaration_id.add(new_var)
                l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) ([0-9]+)\)",r"(_ bv\2 \1)",l)   #(_ bv[num] [size])
                l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) \(- ([0-9]+)\)\)",r"(_ bv-\2 \1)",l)
                if "(set-option" in l:
                    l=re.sub(":"," : ",l)
                new_lines.append(l)

        for l in new_lines:
            l2=l.replace("(","( ").replace(")"," )")
            temp_file.write(l2)
        temp_file.close()
        return input_file+"_temp"

    def parse_stack(self,commands,out_file):
        '''
            creo lo stack, appena becco un checksat faccio il printout considerando anche set-option box/lex
            constructing the data structures
            consideration: looking for set-options, they imply different behaviour
            lex -> use minisearch different cost and constraint constructions
            box -> different file, one for each model

            Possible idea on how to manage push/pop and multiple opt.priority
            generate differente output file for each "section" that is present in the input file
            keep indexes for the objective
        '''

        current_stack=[[]]              #list of list for the stack, the first one is the default one
        file_index=1
        for cmd in commands:
            if cmd.name=='push':
                npush=1
                if cmd.args!=[]:
                    npush=cmd.args[0]
                for _ in range(npush):
                    current_stack.append([])
            elif cmd.name=='pop':
                npop=1
                if cmd.args!=[]:
                    npop=cmd.args[0]
                for _ in range(npop):
                    current_stack.pop()
            elif cmd.name=='check-sat':  #condition to print out
                self.write_stack(current_stack,out_file.replace(".mzn","_"+str(file_index)+".mzn")) #the index variate considering the number of section
                file_index+=1
            else:
                current_stack[-1].append(cmd)

    def write_stack(self,stack,out_file):
        '''
            Write the minizinc file related to each stack
        '''
        flat_stack=[item for l in stack for item in l]
        var_dict={}
        asserts_list=[]
        asserts_soft_list=[]
        commands_list=[]             #maximize/minimize
        set_priority_option="box"    #default value for the case where no option is specified, look for the last one in case
        for el in flat_stack:
            if el.name=='declare-fun' and len(el.args)==1:
                var_dict[str(el.args[0])]=[el.args[0].get_type()]    #rescue the variable type
            elif el.name=='assert':
                asserts_list.append(el.args)
            elif el.name=='assert-soft':
                asserts_soft_list.append(el.args)
            elif el.name=='set-option' and el.args[1]=='opt.priority':  #keep the last one
                set_priority_option=el.args[-1]
            elif el.name=='maximize' or el.name=='minimize':
                commands_list.append((el.name,el.args))
        var_dict=self.modify_type_assert_soft_var(asserts_soft_list,var_dict)
        var_dict=self.add_id_variables_opt(commands_list,var_dict)
        print("Finished to write the stack")
        if len(commands_list)==0:
            self.write_stack_simple(var_dict,asserts_list,asserts_soft_list,out_file)
        else:
            if set_priority_option == 'lex':    #lexicographic order
                self.write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)
            else:                               #box-  also the default one
                self.write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)


    def modify_type_assert_soft_var(self,asserts_soft_list,var_dict):
        '''
            For each group of assert_soft understand the type of the id variable (Reals,Int)
        '''
        dict_type={}
        mgr = get_env()._formula_manager
        for assert_exp in asserts_soft_list:
            if assert_exp[1]==1:
                current_type=mgr.Int(1).get_type()
            else:
                current_type=assert_exp[1].get_type()
            if assert_exp[2] not in dict_type:
                dict_type[assert_exp[2]]=[]
                dict_type[assert_exp[2]].append(current_type)
            else:
                dict_type[assert_exp[2]].append(current_type)
        for k in dict_type:
            if len(set(dict_type[k]))==1:
                var_dict[k]=[dict_type[k][0]]
            else:
                if "Real" in str(dict_type[k]) and "Int" in str(dict_type[k]):   #TODO: add the other cases
                    var_dict[k]=[tp._RealType()]

        return var_dict


    def add_id_variables_opt(self,commands_list,var_dict):
        '''
            Adding the variable related to the id of the maximization and minimization
            and check if it eventually has not been declared yet.
        '''
        id_c=0
        for (_,args) in commands_list:
            args_inner=args[1]
            str_args0 = str(args[0])
            if args[0].size()==1  and ")" not in str_args0 and "(" not in str_args0:  #TODO: review this condition
                expression_type=var_dict[str(args[0])][0]
            else:
                expression_type=args[0].get_type()      #considerare il caso in cui sia una singola variabile e prendere il valore da var_dict
            if ":id" not in args_inner:
                var_id_name="opt_var_"+str(id_c)
                args_inner+=[":id",var_id_name]         #needed to be rescued then
                var_dict[var_id_name]=[expression_type]
                id_c+=1
            else:
                index=args_inner.index(":id")
                var_id_name=args_inner[index+1]
                if var_id_name not in [str(el) for el in var_dict.keys()]:
                    var_dict[var_id_name]=[expression_type]
        return var_dict

    ## ------  LEX STACK ------#

    def write_stack_lex(self,var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
        out_file=out_file.replace(".mzn","l.mzn")
        file_out=open(out_file,"w")
        file_out.write("include \"minisearch.mzn\";\n")
        print("writing variables")
        self.write_list_variables(var_dict,file_out)
        print("writing assertions")
        self.write_assertions(asserts_list,file_out,var_dict)
        print("writing soft")
        self.write_assertions_soft(asserts_soft_list,file_out)
        print("writing maximize/minimize")
        self.write_commands_lex(commands_list,var_dict,file_out)
        file_out.close()

    def write_commands_lex(self,commands_list,var_dict,file_out):
        var_list=[]
        var_list_type=set() #if just one type rescued from the maximize,otherwise use to2float
        mgr = get_env()._formula_manager

        for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
            args_inner=args[1]
            index=args_inner.index(":id") #taking the id value -> equal to the variable
            opt_var=args_inner[index+1]
            var_list_type.add(var_dict[opt_var][0])

        if len(var_list_type)==1:
            final_type=var_list_type.pop()
            if "BV" in str(final_type):
                final_type="int"
            elif "Real" == str(final_type):
                final_type="float"
            elif "Int" == str(final_type):
                final_type="int"
        else:
            raise MultiTypeLexErr("MultiType Lexicographic optimization is not supported")

        for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
            upper=None
            lower=None
            args_inner=args[1]
            index=args_inner.index(":id") #taking the id value -> equal to the variable
            opt_var=args_inner[index+1] #temp variable (d'appoggio) to maximize or minimize
            objective_arg = args[0] #FNODE type -> parsed with get_expression

            if ":upper" in args_inner:
                index=args_inner.index(":upper")
                upper=args_inner[index+1] #Fnode
            if ":lower" in args_inner:
                index=args_inner.index(":lower")
                lower=args_inner[index+1] #Fnode
            try:
                signed=args_inner.index(":signed")
            except ValueError:
                signed=-1
            if objective_arg.size() == 1: #name of a variable
                objective_arg=mgr._create_symbol(str(args[0]),typename=var_dict[str(args[0])][0])

            opt_symbol = mgr._create_symbol(opt_var,var_dict[opt_var][0])
            assignment = mgr.Equals(opt_symbol,objective_arg)
            file_out.write("constraint ("+self.serializer.serialize(assignment,daggify=False)+");\n")

            opt_symbol_lex = mgr._create_symbol(opt_var+"_lex",var_dict[opt_var][0])
            lex_type = "int" if "BV" in str(var_dict[opt_var][0]) else str(var_dict[opt_var][0]).lower()
            file_out.write("var %s:%s;\n "%(lex_type,opt_symbol_lex))
            if name=="maximize" and "BV" not in str(var_dict[opt_var][0]):
                opt_symbol_tmp = mgr.Minus(mgr.Int(0),opt_symbol)
                assignment = mgr.Equals(opt_symbol_lex,opt_symbol_tmp)
                file_out.write("constraint ("+self.serializer.serialize(assignment,daggify=False)+");\n")
            elif name=="maximize" and "BV" in str(var_dict[opt_var][0]) and signed==-1: #maximization BV8 unisgned -> max value is 255 -> minimize 255-opt_symbol
                file_out.write("constraint( %s = %s - %s );\n"%(opt_symbol_lex,pow(2,opt_symbol.bv_width())-1,opt_symbol))
            elif name=="maximize" and "BV" in str(var_dict[opt_var][0]) and signed>-1: #maximization BV8 signed -> maxvalue is 127 -> minimize 127-opt_symbol
                file_out.write("constraint( %s = %s - (-%s*((%s div %s) mod 2))+sum([pow(2,i)*((%s div pow(2,i)) mod 2)| i in 0..%s-1] ));\n"
                               %(opt_symbol_lex,pow(2,opt_symbol.bv_width()-1)-1,pow(2,opt_symbol.bv_width()-1),opt_symbol,pow(2,opt_symbol.bv_width()-1),opt_symbol,opt_symbol.bv_width()-1))
            elif name=="minimize" and "BV" in str(var_dict[opt_var][0]) and signed>-1: #maximization BV8 signed -> maxvalue is 127 -> minimize 127-opt_symbol
                file_out.write("constraint( %s = (-%s*((%s div %s) mod 2))+sum([pow(2,i)*((%s div pow(2,i)) mod 2)| i in 0..%s-1] ));\n"
                               %(opt_symbol_lex,pow(2,opt_symbol.bv_width()-1),opt_symbol,pow(2,opt_symbol.bv_width()-1),opt_symbol,opt_symbol.bv_width()-1))
            else:
                assignment = mgr.Equals(opt_symbol,opt_symbol_lex)
                file_out.write("constraint ("+self.serializer.serialize(assignment,daggify=False)+");\n")
            if upper is not None:
                if "BV" in str(upper.get_type()):
                    file_out.write("constraint(%s >= %s /\ %s <= %s);\n"%(opt_symbol,0,opt_symbol,pow(2,opt_symbol.bv_width())-1))
                    if signed>=0:
                        less_than = mgr.BVSLE(opt_symbol,upper)
                    else:
                        less_than = mgr.BVULE(opt_symbol,upper)
                    file_out.write("constraint ("+self.serializer.serialize(less_than)+");\n")
                else:
                    less_than = mgr.LE(opt_symbol,upper)
                    file_out.write("constraint ("+self.serializer.serialize(less_than,daggify=False)+");\n")
            if lower is not None:
                if "BV" in str(lower.get_type()):
                    file_out.write("constraint(%s >= %s /\ %s <= %s);\n"%(opt_symbol,0,opt_symbol,pow(2,opt_symbol.bv_width())-1))
                    if signed>=0:
                        less_than = mgr.BVSLE(lower,opt_symbol)
                    else:
                        less_than = mgr.BVULE(lower,opt_symbol)
                    file_out.write("constraint ("+self.serializer.serialize(less_than)+");\n")
                else:
                    less_than = mgr.LE(lower,opt_symbol)
                    file_out.write("constraint ("+self.serializer.serialize(less_than,daggify=False)+");\n")
            var_list.append(opt_symbol_lex)
        file_out.write("array[int] of var "+str(final_type)+": obj_array;\n")
        file_out.write("obj_array=[")
        file_out.write(str(var_list[0]))
        for el in var_list[1:]:
            file_out.write(","+str(el))
        file_out.write("];\n")
        file_out.write("%using minisearch\n")
        file_out.write("solve search minimize_lex_pers(obj_array);\n")



        ##Minisearch Paper Implementation
        file_out.write("""\n
    function ann : minimize_lex_pers(array[int] of var """+str(final_type)+""" : objs) =
        next() /\ commit() /\ print() /\\
        repeat( scope(
            post(lex_less(objs, [sol(objs[i]) | i in index_set(objs)])) /\\
            if next() then commit() /\ print() else break endif ) );
    """)

    ## ------  END   LEX ------##
    ## ------  BOX STACK ------##


    def write_stack_box(self,var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
        '''
            For each function to maximize or to minize create a new file,
            keep the assignement to the optimization variables on all the files but not the upper
            and lower constraints
        '''
        i=0
        common_lines=[]
        unique_lower=[]
        unique_upper=[]
        mgr = get_env()._formula_manager
        signed = -1
        for (name,args) in commands_list: #argslist [cost_function,[parameter]]
            upper=None
            lower=None
            args_inner=args[1]
            index=args_inner.index(":id")
            opt_var=args_inner[index+1] #temp variable (d'appoggio) to maximize or minimize
            objective_arg = args[0] #FNODE type -> parsed with get_expression
            try:
                signed=args_inner.index(":signed")
            except ValueError:
                signed=-1
            #writing the maximize and the minimize
            if ":upper" in args_inner:
                index=args_inner.index(":upper")
                upper=args_inner[index+1]
            if ":lower" in args_inner:
                index=args_inner.index(":lower")
                lower=args_inner[index+1]
            if objective_arg.size() == 1: #name of a variable
                objective_arg=mgr._create_symbol(str(args[0]),typename=var_dict[str(args[0])][0])
            opt_symbol = mgr._create_symbol(opt_var,var_dict[opt_var][0])
            assignment = mgr.Equals(opt_symbol,objective_arg)
            common_lines.append("constraint ("+self.serializer.serialize(assignment,daggify=False)+");\n")
            #opt_Var and opt_symbol are the same
            if upper is not None:
                if "BV" in str(upper.get_type()):
                    if signed>=0:
                        less_than = mgr.BVSLE(opt_symbol,upper)
                    else:
                        less_than = mgr.BVULE(opt_symbol,upper)
                    unique_upper.append("constraint ("+self.serializer.serialize(less_than)+");\n")
                else:
                    less_than = mgr.LE(opt_symbol,upper)
                    unique_upper.append("constraint ("+self.serializer.serialize(less_than,daggify=False)+");\n")
            else:
                unique_upper.append(" ")
            if lower is not None:
                if "BV" in str(lower.get_type()):
                    if signed>=0:
                        less_than = mgr.BVSLE(lower,opt_symbol)
                    else:
                        less_than = mgr.BVULE(lower,opt_symbol)
                    unique_lower.append("constraint ("+self.serializer.serialize(less_than)+");\n")
                else:
                    less_than = mgr.LE(lower,opt_symbol)
                    unique_lower.append("constraint ("+self.serializer.serialize(less_than,daggify=False)+");\n")
            else:
                unique_lower.append(" ")
        for (name,args) in commands_list:
            i+=1
            file_out=open(out_file.replace(".mzn","_b"+str(i))+".mzn","w")
            print("writing variables")
            self.write_list_variables(var_dict,file_out)
            print("writing assertions")
            self.write_assertions(asserts_list,file_out,var_dict)
            print("writing soft")
            self.write_assertions_soft(asserts_soft_list,file_out)
            print("writing maximize/minimize")
            for line in common_lines:
                file_out.write(line)
            file_out.write(unique_lower[i-1]) #same list as command_list
            file_out.write(unique_upper[i-1]) #same list as command_list
            args_inner=args[1]
            index=args_inner.index(":id")
            opt_var=args_inner[index+1]
            opt_symbol = mgr._create_symbol(opt_var,var_dict[opt_var][0])
            try:
                signed=args_inner.index(":signed")
            except ValueError:
                signed=-1
            if name=='maximize': #qui si puo decidere facilmente se con segno o no, basta vedere se signed
                if "BV" in str(var_dict[opt_var][0]):
                    file_out.write("constraint(%s >= %s /\ %s <= %s);\n"%(opt_symbol,0,opt_symbol,pow(2,opt_symbol.bv_width())-1))
                    if signed!=-1:
                        file_out.write("solve maximize (-%s*((%s div %s) mod 2))+sum([pow(2,i)*((%s div pow(2,i)) mod 2)| i in 0..%s-1]);\n"
                                                        %(pow(2,opt_symbol.bv_width()-1),opt_symbol,pow(2,opt_symbol.bv_width()-1),opt_symbol,opt_symbol.bv_width()-1))
                    else:
                        #bound = mgr.And(mgr.BVULE(opt_symbol,mgr.BV(pow(2,opt_symbol.bv_width())-1,width=opt_symbol.bv_width())),mgr.BVUGE(opt_symbol,mgr.BV(0,width=opt_symbol.bv_width())))
                        #file_out.write("constraint ("+self.serializer.serialize(bound)+");\n")
                        file_out.write("solve maximize "+opt_var+";\n")
                else:
                    file_out.write("solve maximize "+opt_var+";\n")
            else:
                if "BV" in str(var_dict[opt_var][0]):
                    file_out.write("constraint(%s >= %s /\ %s <= %s);\n"%(opt_symbol,0,opt_symbol,pow(2,opt_symbol.bv_width())-1))
                    if signed!=-1:
                        file_out.write("solve minimize (-%s*((%s div %s) mod 2))+sum([pow(2,i)*((%s div pow(2,i)) mod 2)| i in 0..%s-1]);\n"
                                                        %(pow(2,opt_symbol.bv_width()-1),opt_symbol,pow(2,opt_symbol.bv_width()-1),opt_symbol,opt_symbol.bv_width()-1))
                    else:
                        #bound = mgr.And(mgr.BVULE(opt_symbol,mgr.BV(pow(2,opt_symbol.bv_width())-1,width=opt_symbol.bv_width())),mgr.BVUGE(opt_symbol,mgr.BV(0,width=opt_symbol.bv_width())))
                        #file_out.write("constraint ("+self.serializer.serialize(bound)+");\n")

                        file_out.write("solve minimize "+opt_var+";\n")
                else:
                    file_out.write("solve minimize "+opt_var+";\n")

            file_out.write("output [ \"opt_var = \",show("+opt_var+")]")
            file_out.close()

    ## ------  END BOX ------##

    def write_stack_simple(self,var_dict,asserts_list,asserts_soft_list,out_file):
        out_file=out_file.replace(".mzn","s.mzn")
        file_out=open(out_file,"w")
        print("writing variables")
        self.write_list_variables(var_dict,file_out)
        print("writing assertions")
        self.write_assertions(asserts_list,file_out,var_dict)
        print("writing soft")
        self.write_assertions_soft(asserts_soft_list,file_out)
        print("writing satisfy")
        file_out.write("solve satisfy;\n")
        file_out.close()

    def write_list_variables(self,variables,file_out):
        '''
            Writes list of the variables in mzn
        '''
        for var in variables.keys():
            #In minizinc if no domain is specified there can be problems with the solver like g12
            bv_search=re.search(r"BV{([0-9]+)}",str(variables[var][0]))
            if bv_search:
                file_out.write("var 0.."+str(pow(2,int(bv_search.groups(0)[0]))-1)+" : "+str(var)+";\n")
                #   file_out.write("constraint("+str(var)+">=0 /\ "+str(pow(2,int(bv_search.groups(0)[0])))+" > "+str(var)+");\n")
            elif "Real" in str(variables[var][0]):
                if self.float_domains==0:
                    file_out.write("var -2147483648.0..2147483648.0: "+str(var)+";\n")
                else:
                    file_out.write("var -3.402823e+38..3.402823e+38 : "+str(var)+";\n")
                #file_out.write("var float : "+str(var)+";\n")
            else:
                typeD=variables[var][0]
                file_out.write("var "+str(typeD).lower()+":"+str(var)+";\n")


    def write_assertions(self,asserts_list,file_out,var_dict):
        '''
            Write the list of assertion

        '''
        if self.flag_bigand==True: #necessary bigand
            mgr = get_env()._formula_manager
            bigAnd=asserts_list[0][0]
            tmp_ris=None
            for ind in xrange(1,len(asserts_list)):
                if type(asserts_list[ind]) is list:
                    tmp=asserts_list[ind][0]
                else:
                    tmp=asserts_list[ind]
                tmp_ris=mgr.And(bigAnd,tmp)
                bigAnd=tmp_ris
            self.serializer.serialize(bigAnd,output_file=file_out)
        else:
            for el in asserts_list:
                if type(el) is list:
                    el=el[0]
                self.serializer.serialize(el,output_file=file_out)

    def write_assertions_soft(self,asserts_soft_list,file_out):
        '''
            Writing the soft assertions list
            for each group of assertion with the same id add its related group of constraint
            (assert-soft a :weight expr1 :id goal)
            (assert-soft b :weight expr2 :id goal)
            -----
            (constraint bv_goal_1=a)
            (constraint bv_goal_2=b)
            (constraint bv_goal = not(a)*expr1 + not(b)*expr2)
        '''

        cost_variables_set = set([l[-1] for l in asserts_soft_list]) #one variable for each of them
        var_index = {name:0 for name in cost_variables_set}
        var_weight = {}
        for el in asserts_soft_list:
            file_out.write("var bool:"+el[-1]+"_"+str(var_index[el[-1]])+";\n")

            ris=self.serializer.serialize(el[0])
            file_out.write("constraint ("+el[-1]+"_"+str(var_index[el[-1]])+" = "+ris+");\n")
            var_weight[el[-1]+"_"+str(var_index[el[-1]])]=self.serializer.serialize(el[1],daggify=False)
            var_index[el[-1]]+=1
        for cost in cost_variables_set:
            file_out.write("constraint ("+cost+"=")
            str_ap=[]
            for k in var_weight:
                if cost in k:
                    str_ap.append("not("+str(k)+")*("+str(var_weight[k])+")")

            file_out.write("+".join(str_ap)+");\n")
            str_ap=[]
            for k in var_weight:
                if cost in k and eval(var_weight[k])<0:
                    str_ap.append("("+str(var_weight[k])+")")

            file_out.write("constraint (( ")
            if len(str_ap)==0:
                file_out.write("0)")
            else:
                file_out.write("+".join(str_ap)+") ")
            file_out.write(" <= "+cost+" /\ "+cost+" <= (")
            str_ap=[]
            for k in var_weight:
                if cost in k and eval(var_weight[k])>=0:
                    str_ap.append("("+str(var_weight[k])+")")
            if len(str_ap)==0:
                file_out.write("0));\n")
            else:
                file_out.write("+".join(str_ap)+"));\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", help="smt2 input file path")
    parser.add_argument("output_file", help="mzn output file path")
    parser.add_argument("--asoft_var_type",type=str,default="Real",choices=["Real","Int"],help="Set type for all the assert-soft variables")
    parser.add_argument("--big_and", action="store_true",default=False, help="if used this option allows to merge all the asserts in only one big assert")
    parser.add_argument("--max_int_bit_size",type=int,default=32,choices=[32,64],help="""define the size of the integer variable used by the mzn solver.\n
                                                                                                Is useful for the BV problems.\n
                                                                                                The default values is 32. The possible values are 32,64""")
    parser.add_argument("--printer_opt",type=int,default=0,choices=[0,1],help="""0: Default daggify print, it creates a new scopes for every subformula\n
                                                                        1: 2 Fathers daggify print, it creates a labeling exclusively for every boolean subformula with 2 fathers in the formula DAG""")
    parser.add_argument("--float_domains",type=int,default=0,choices=[0,1],help=" Float Domains options -> 0:-2147483648.0..2147483648.0  1:-3.402823e+38..3.402823e+38 ")
    args = parser.parse_args()
    parser=Omt2Mzn(args.input_file,args.output_file,args.big_and,args.max_int_bit_size,args.printer_opt,args.asoft_var_type,args.float_domains)
    parser.startParsing()
