'''
Francesco Contaldo 2018 
A python parser omt2mzn
#TODO: parte di asset-soft BV, passing her variables_dict.keys()
#TODO: risolvere la questione di bitvector per le operazioni con il segno
#TODO: completare il parsing
#TODO: inside the parser i first try to parse in SBV then BV
#TODO: manage the sign

function array[int] of var bool : sumBV(array[1..4] of var bool: b, array[1..4] of var bool: a) = 
              [(a[i] xor b[i]) xor (a[i+1] /\ b[i+1]) | i in reverse(1..3)] ++ [a[4] xor b[4]];                   

'''
from pyomt.smtlib.parser import SmtLib20Parser
from pyomt.printers_mzn import HRSerializer
from pyomt.environment import get_env
import sys
import re
import os


class WrongNumbArgs(StandardError):
    pass

def pre_proc(input_file):
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
                    new_lines.append("\n(declare-fun "+new_var+" () Real)\n")
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

def modify_type_assert_soft(asserts_soft_list,var_dict):
    '''
        The variable here as been declared automatically Real(float), then
        it is necessary to infer from all the weights its real type
    '''
    dict_type={}
    for assert_exp in asserts_soft_list:
        #assert_exp [expression(Fnode),assert_soft_id]
        if assert_exp[1]==1:
            current_type="Int"
        else:
            current_type=assert_exp[1].get_type()
        if assert_exp[2] not in dict_type:
            dict_type[assert_exp[2]]=[]
            dict_type[assert_exp[2]].append(str(current_type))
        else:
            dict_type[assert_exp[2]].append(str(current_type))
    for k in dict_type:
        if len(set(dict_type[k]))==1:
            var_dict[k]=[dict_type[k][0]]
        else:
            if "Real" in dict_type[k] and "Int" in dict_type[k]: #TODO: add the other cases
                var_dict[k]=["Real"]
    return var_dict


def add_id_variables_opt(commands_list,var_dict):
    '''
        Adding the variable related to the id of the maximization and minimization
        and check if it eventually has not been declared yet.
    '''
    id_c=0
    for (name,args) in commands_list:
        args_inner=args[1]
        expression_type=args[0].get_type()
        if ":id" not in args_inner:
            var_id_name="opt_var_"+str(id_c)
            args_inner+=[":id",var_id_name] #needed to be rescued then
            var_dict[var_id_name]=[expression_type]
            id_c+=1
        else:
            index=args_inner.index(":id")
            var_id_name=args_inner[index+1]
            if var_id_name not in [str(el) for el in var_dict.keys()]:
                var_dict[var_id_name]=[expression_type]
    return var_dict

def retrieve_presence_bv(var_dict):
    '''
        Rescue all the lenghts related to all the BV variables
    '''
    for var in var_dict.keys():
        bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[var][0]))
        if bv_search:
            return True
    return False

def write_list_variables(variables,file_out):
    '''
        Writes list of the variables
    '''
    bv_len=0
    for var in variables.keys():
        #In minizinc if no domain is specified there can be problems with the solver like g12
        bv_search=re.search(r"BV{([0-9]+)}",str(variables[var][0]))
        if bv_search:
            bv_len,=bv_search.groups()
            file_out.write("array[1.."+bv_len+"] of var bool:"+str(var)+";\n")           
        elif "Real" in str(variables[var][0]):
            file_out.write("var -2147483646.0..2147483646.0 : "+str(var)+";\n")
            #file_out.write("var float : "+str(var)+";\n")  
        else:
            type=variables[var][0]
            file_out.write("var "+str(type).lower()+":"+str(var)+";\n")


def write_assertions(asserts_list,file_out,var_dict):
    '''
        Write the list of assertion
        reference: https://github.com/hakank/hakank/blob/master/minizinc/bit_vector1.mzn
        modulo sum in minizinc
        function array[int] of var bool : sumBV(array[1..4] of var bool: b, array[1..4] of var bool: a) = 
                                                                                                 [(a[i] xor b[i]) xor (a[i+1] /\ b[i+1]) | i in reverse(1..3)] ++ [a[4] xor b[4]];
    '''
    
    '''
    bv_len_list=retrieve_bv_lengths(var_dict)
    for bv_lenght in bv_len_list: #for each possible length declare a function of the same length
        file_out.write("function var int: toNumSigned"+str(bv_lenght)+"(array[1.."+str(bv_lenght)+"] of var bool: a) = -ceil(pow(2,"+str(bv_lenght)+"-1))*a[1]+"+"sum([ceil(pow(2,"+str(bv_lenght)+"-i)) * a[i]| i in 2.."+str(bv_lenght)+"]);\n")
        file_out.write("function var int: toNum"+str(bv_lenght)+"(array[1.."+str(bv_lenght)+"] of var bool: a) = sum([ceil(pow(2,"+str(bv_lenght)+"-i)) * a[i]| i in 1.."+str(bv_lenght)+"]);\n")
        file_out.write("function array[int] of var bool: sumBV(array[1.."+str(bv_lenght)+"] of var bool: a, array[1.."+str(bv_lenght)+"] of var bool b) =\n   [(a[i] xor b[i]) xor (a[i+1] /\\ b[i+1]) | i in reverse(1.."+str(bv_lenght-1)+")] ++ [a["+str(bv_lenght)+"] /\\ b["+str(bv_lenght)+"]]; ")
        function array[int] of var bool : bvcomp(array[int] of var bool: a,int: i,int: j) =
                                  [a[k] | k in i..j];
    '''
    if retrieve_presence_bv(var_dict):
        file_out.write("\n%BitVector Function Definition\n")
        file_out.write("\nfunction var int: toNumS (array[int] of var bool: a) = \n -ceil(pow(2,length(a)-1))*a[1]+sum([ceil(pow(2,length(a)-i)) * a[i]| i in 2..length(a)]);\n")
        file_out.write("\nfunction var int: toNum (array[int] of var bool: a) = \n  sum([ceil(pow(2,length(a)-i)) * a[i]| i in 1..length(a)]);\n")
        file_out.write("\nfunction array[int] of var bool: sumBV(array[int] of var bool: a, array[int] of var bool: b) =\n   [(a[i] xor b[i]) xor (a[i+1] /\\ b[i+1]) | i in reverse(1..length(a)-1)] ++ [a[length(a)] /\\ b[length(b)]]; ")
        file_out.write("\nfunction array[int] of var bool: extractBV(array[int] of var bool: a,int: i,int: j) = \n  [a[k] | k in i..j];\n\n")
        file_out.write("""\npredicate bvcomp(array [$T] of var bool: x, array [$T] of var bool: y) =
    let {
        array [int] of var bool: xx = array1d(x), 
        array [int] of var bool: yy = array1d(y),
    } in (assert(index_sets_agree(x, y), "array index sets do not match", 
        forall ( i in index_set(xx) ) ( 
        not(xx[i] xor yy[i]) ))
    );\n""")
    for el in asserts_list:
        if type(el) is list:
            el=el[0]
        serializer=HRSerializer()
        file_out.write("constraint ("+serializer.serialize(el)+");\n")
        
def write_assertions_soft(asserts_soft_list,file_out):
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
        serializer=HRSerializer()
        ris=serializer.serialize(el)
        file_out.write("constraint ("+el[-1]+"_"+str(var_index[el[-1]])+"="+ris+");\n")
        var_weight[el[-1]+"_"+str(var_index[el[-1]])]=el[1]
        var_index[el[-1]]+=1
    for cost in cost_variables_set:
        file_out.write("constraint ("+cost+"=")
        str_ap=[]
        for k in var_weight:
            if cost in k:
                str_ap.append("not("+str(k)+")*"+str(var_weight[k]))
        file_out.write("+".join(str_ap)+");\n")
        file_out.write("constraint ( 0 <= "+cost+" /\ "+cost+" <= (")
        str_ap=[]
        for k in var_weight:
            if cost in k:
                str_ap.append(str(var_weight[k]))
        file_out.write("+".join(str_ap)+"));\n")

def write_commands_lex(commands_list,var_dict,file_out):
    var_list=[]
    var_list_type=set() #if just one type rescued from the maximize,otherwise use to2float
    flag_change=0
    mgr = get_env()._formula_manager
    serializer=HRSerializer()
    for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
        args_inner=args[1]
        index=args_inner.index(":id") #taking the id value -> equal to the variable
        opt_var=args_inner[index+1]
        var_list_type.add(var_dict[opt_var][0]) 
        var_list.append(opt_var)
    if len(var_list_type)==1:
        final_type=var_list_type.pop()
        if "BV" in str(final_type):
            final_type="int"
    elif len(var_list_type)==2 and "int" in var_list and "BV" in var_list_type:
        final_type="int"
    else:
        final_type="float"
        var_list2=[] #add opt_variables to change their type
        flag_change=1
        for var_name in var_list:
            type_to_check = str(var_dict[var_name][0])
            if type_to_check=="Int" or type_to_check=="int" or "BV" in type_to_check:
                opt_var_name=var_name+"_f"
                file_out.write("var float: "+opt_var_name+";\n")
                var_list2.append(opt_var_name)
            else:
                var_list2.append(var_name)             
        var_list=var_list2

    for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
        upper=None
        lower=None
        args_inner=args[1]
        index=args_inner.index(":id") #taking the id value -> equal to the variable
        opt_var=args_inner[index+1]
        if ":upper" in args_inner:
            index=args_inner.index(":upper")
            upper=args_inner[index+1] #Fnode
        if ":lower" in args:
            index=args_inner.index(":lower")
            lower=args_inner[index+1] #Fnode
        try:
            signed=args_inner.index(":signed") 
        except ValueError:
            signed=-1
        
        objective_arg = args[0]
        if "BV" in var_dict[opt_var][0]: #devo creare una variabile int per il toNum
            file_out.write("var int: "+opt_var+"_BV2INT"+";\n") #TODO: fare il cambio per il lex int no float
            opt_symbol_int = mgr._create_symbol(opt_var+"_BV2INT",typename=types.INT) 
            opt_symbol_bv = mgr._create_symbol(opt_var,var_dict[opt_var][0])
            assignment_bv = (opt_symbol_bv,objective_arg)
            assignment_toNum = mgr.Equals(opt_symbol_int,opt_symbol_bv)
            file_out.write("constraint ("+serializer.serialize(assignment+");\n")) #bv = objective in bv
            str_to_write = serializer.serialize(assignment_toNum)
            if signed == -1:
                str_to_write = re.replace(r"(.*) = (.*)",r"\1 = toNum(\2)",str_to_write)
            else:
                str_to_write = re.replace(r"(.*) = (.*)",r"\1 = toNumS(\2)",str_to_write)
            if name == "maximize":
                str_to_write = re.replace(r"(.*) = (.*)",r"\1 = -(\2)",str_to_write)
                file_out.write("constraint ("+str_to_write+");\n")
            else:
                file_out.write("constraint ("+str_to_write+");\n") # bv2int = bv 
            if flag_change and opt_var+"_f" in var_list:
                file_out.write("constraint("+opt_var+"_f=int2float("+opt_var+"_BV2INT));\n")
            else:
                index_optvarBV=var_list.index(opt_var)
                var_list.remove(opt_var)
                var_list.insert(index_optvarBV,opt_var+"_BV2INT")
        else: 
            opt_symbol = mgr._create_symbol(opt_var,var_dict[opt_var][0])
            if name=="maximize":
                objective_arg_neg = mgr.Minus(mgr.Int(0),objective_arg)
                assignment = mgr.Equals(opt_symbol,objective_arg_neg)
            else:
                assignment = mgr.Equals(opt_symbol,objective_arg)
            file_out.write("constraint ("+serializer.serialize(assignment+");\n"))  
            if flag_change and opt_var+"_f" in var_list:
                    file_out.write("constraint("+opt_var+"_f=int2float("+opt_var+"));\n")


        if upper is not None:
            if "BV" in str(upper.get_type()):
                if signed>=0:
                    less_than = mgr.BVSLE(opt_symbol,upper)
                else:
                    less_than = mgr.BVULE(opt_symbol,upper)
            else:
                less_than = mgr.LE(opt_symbol,upper)
            file_out.write("constraint ("+serializer.serialize(less_than)+");\n")
        if lower is not None:
            if "BV" in str(lower.get_type()):
                if signed>=0:
                    less_than = mgr.BVSLE(lower,opt_symbol)
                else:
                    less_than = mgr.BVULE(lower,opt_symbol)
            else:
                less_than = mgr.LE(lower,opt_symbol)
            file_out.write("constraint ("+serializer.serialize(less_than)+");\n")
    
    file_out.write("array[int] of var "+final_type+": obj_array;\n")
    file_out.write("obj_array=[")
    file_out.write(var_list[0])
    for el in var_list[1:]:
        file_out.write(","+el)
    file_out.write("];\n")
    file_out.write("%use minisearch\n")
    file_out.write("solve search minimize_lex_pers(obj_array);\n")
    ##PAPER Implementation
    file_out.write("""\n
function ann : minimize_lex_pers(array[int] of var """+type+""" : objs) =
    next () /\ commit () /\\
    repeat(
        scope(
            post(lex_less(objs,[sol(objs[i]) | i in index_set (objs)])) /\\
            if next() then commit () else print() /\ break endif
    ));
""")

def write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
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
    serializer=HRSerializer()
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
        opt_symbol = mgr._create_symbol(opt_var,var_dict[opt_var][0])
        assignment = mgr.Equals(opt_symbol,objective_arg)
        common_lines.append("constraint ("+serializer.serialize(assignment)+");\n")
        if upper is not None:
            if "BV" in str(upper.get_type()):
                if signed>=0:
                    less_than = mgr.BVSLE(opt_symbol,upper)
                else:
                    less_than = mgr.BVULE(opt_symbol,upper)
            else:
                less_than = mgr.LE(opt_symbol,upper)
            unique_upper.append("constraint ("+serializer.serialize(less_than)+");\n")
        else:
            unique_upper.append("")
        if lower is not None:
            if "BV" in str(lower.get_type()):
                if signed>=0:
                    less_than = mgr.BVSLE(lower,opt_symbol)
                else:
                    less_than = mgr.BVULE(lower,opt_symbol)
            else:
                less_than = mgr.LE(lower,opt_symbol)
            unique_upper.append("constraint ("+serializer.serialize(less_than)+");\n")
        else:
            unique_lower.append("")
    for (name,args) in commands_list:
        i+=1
        file_out=open(out_file.replace(".mzn","_b"+str(i))+".mzn","w")
        file_out.write("include \"globals.mzn\";\n")
        write_list_variables(var_dict,file_out)
        write_assertions(asserts_list,file_out,var_dict)
        write_assertions_soft(asserts_soft_list,file_out)
        for line in common_lines:
            file_out.write(line)
        file_out.write(unique_lower[i-1]) #same list as command_list
        file_out.write(unique_upper[i-1]) #same list as command_list
        args_inner=args[1]
        index=args_inner.index(":id")
        opt_var=args_inner[index+1]
        try:
            signed=args_inner.index(":signed") 
        except ValueError:
            signed=-1
        if name=='maximize': #qui si puo decidere facilmente se con segno o no, basta vedere se signed
            if "BV" in str(var_dict[opt_var][0]):
                if signed!=-1:
                    file_out.write("solve maximize toNumS("+opt_var+");\n")
                else:
                    file_out.write("solve maximize toNum("+opt_var+");\n")
            else:
                file_out.write("solve maximize "+opt_var+";\n")
        else:
            if "BV" in str(var_dict[opt_var][0]):
                if signed!=-1:
                    file_out.write("solve minimize toNumS("+opt_var+");\n")
                else:
                    file_out.write("solve minimize toNum("+opt_var+");\n")
            else:
                file_out.write("solve minimize "+opt_var+";\n")
        file_out.close()

def write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
    file_out=open(out_file,"w")
    file_out.write("include \"globals.mzn\";\n")
    file_out.write("include \"minisearch.mzn\";\n")
    write_list_variables(var_dict,file_out)
    write_assertions(asserts_list,file_out,var_dict)
    write_assertions_soft(asserts_soft_list,file_out)
    write_commands_lex(commands_list,var_dict,file_out)
    file_out.close()


def write_stack(stack,out_file):
    '''
        Write the minizinc file related to each stacks
    '''
    flat_stack=[item for l in stack for item in l]
    var_dict={}
    asserts_list=[]
    define_fun_list={}
    asserts_soft_list=[]
    commands_list=[]             #maximize/minimize
    set_priority_option="box"    #default value for the case where no option is specified, look for the last one in case
    for el in flat_stack:
        if el.name=='declare-fun' and len(el.args)==1: 
            var_dict[str(el.args[0])]=[el.args[0].get_type()]   #rescue the variable type
        elif el.name=='define-fun' and len(el.args)==2:         #treat them as constraint
            define_fun_list[str(el.args[0])]=[el.args[1:]]      #empty,type,expression
        elif el.name=='assert':
            asserts_list.append(el.args)
        elif el.name=='assert-soft':
            asserts_soft_list.append(el.args)
        elif el.name=='set-option' and el.args[0]==':opt.priority':  #keep the last one
            set_priority_option=el.args[1]
        elif el.name=='maximize' or el.name=='minimize':
            commands_list.append((el.name,el.args))
    var_dict=add_id_variables_opt(commands_list,var_dict)
    var_dict=modify_type_assert_soft(asserts_soft_list,var_dict) #TODO:review
    print("Finished to create the structures")
    if set_priority_option == 'lex':    #lexicographic order 
        write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)
    else:                               #box-  also the default one
        write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)

def parse_stack(commands,out_file):
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
    
    current_stack=[[]] #list of list for the stack, the first one is the default one
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
            write_stack(current_stack,out_file.replace(".","_"+str(file_index)+"."))
            file_index+=1
        else:
            current_stack[-1].append(cmd)
        
               
def startParsing(input_file,out_file):
    parser = SmtLib20Parser() 
    new_input_f = pre_proc(input_file)
    script = parser.get_script_fname(new_input_f)
    print("Parsing form pyomt is complete")
    commands = script.commands      #getting the list of commands (set-option,set-logic,declaration,assert,command)         
    parse_stack(commands,out_file)  #calling the main function
    os.remove(new_input_f)
  
if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs("Incorrect number of arguments")
    else:
        startParsing(sys.argv[1],sys.argv[2])