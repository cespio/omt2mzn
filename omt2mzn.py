'''
Francesco Contaldo 2018 
A python parser omt2mnz

Linear Arithmetic (Integer & Real) | QF_LIA QF_LRA
Non Linear Arithmetic  (Integer & Real) | QF_NIA QF_NRA
BitVector | QF_BV

Minisearch solo per int e non real

- BitVector in boolean
- #self.walk(f, threshold=9999999999999999999) printers.py l45- 

Keeping the original type of the variables can be done
the different problem arises
1]What happen in lexicographic order? float/int can't be done -> also only float can be done
2]type of the assert soft variables -> should be deduced from its weight [look up at each weight function]
3]type of the variables to be optimized [the one related to minimize/maximize] -> infer the type of the expression
    keeping in the consideration the transformation that have been taken during the preprocessing
4]take into consideration also the int2float, float2int

    
    Here perform the variables typechecking -> before writing
    1] variables declaration
    2] assert soft
    3] variable to optimazie, considerare l'espressione e in caso metterla float
    var_dict=add_id_variables(commands_list,var_dict,were_int)
    var_dict=adjust_type_var(var_dict,were_int)
    var_dict=adjust_assert_soft_var(var_dict,asserts_soft_list,were_int)


#TODO: parte di asset-soft BV, passing her variables_dict.keys()
#TODO: parsing con minimize/maximize sui bitvector poi funzione lexicographic
#TODO: ricordarsi di sostituire i valori #b01010
#TODO: in box per BV ricordarsi su come gestire gli assegnamenti
#TODO: ricordarsi di gestire int real -> per adesso tutto in real
'''
from pyomt.smtlib.parser import *
from pyomt.exceptions import *
import pyomt
import sys
import re


class WrongNumbArgs(StandardError):
    pass
class NoLogicDefined(StandardError):
    pass
class BVtoLexicographic(StandardError):
    pass

def pre_proc(input_file):
    lines=open(input_file).readlines()
    temp_file=open(input_file+"_temp","w")
    #flagReal=1 #transofrm everyting to real even if not strictly necessary
    nl=[] #new_lines
    set_declaration_id=set() #variable declaration for assert soft, make sure it is unique
    for l in lines:
        if l[0]!=";": #skipping comment line
            l=re.sub(r";.*","",l) #deleting comment in the same line
            '''
            int_search=re.search(r"(declare-fun (.+) \(\) Int)",l)
            if int_search:
                (_,toAdd)=int_search.groups()
                wereInt.append(toAdd)
            '''
            if "assert-soft" in l:
                if ":id " in l:
                    new_var = l.split(":id")[-1].strip().replace(")","")
                else:
                    new_var = "I"
                if new_var not in set_declaration_id:
                    nl.append("\n;declaration of additional variable for assert-soft\n")
                    nl.append("\n(declare-fun "+new_var+" () Real)\n")
                    set_declaration_id.add(new_var)
            #bv operations
            #(_ bv[num] [size])
            l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) ([0-9]+)\)",r"(_ bv\2 \1)",l)
            l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) \(- ([0-9]+)\)\)",r"(_ bv-\2 \1)",l)
            '''
            bv_search=re.search(r"\(\(\_ to\_bv ([0-9]+)\) ([0-9]+)\)",l) #this is necesarry because pysmt do not support _to_bv
            if bv_search:
                (a1,a2)=bv_search.groups()
                bv=str('{0:0'+a1+'b}').format(int(a2))        
                l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) ([0-9]+)\)","#b"+bv,l)
            bv_search=re.search(r"\(\(\_ to\_bv ([0-9]+)\) \(- ([0-9]+)\)\)",l)
            if bv_search:
                (a1,a2)=bv_search.groups()
                bv=str('{0:0'+str(int(a1)-1)+'b}').format(int(a2))
                l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) \(- ([0-9]+)\)\)","#b1"+bv,l)
            '''
            nl.append(l)
            
    lines=nl
    for l in nl:
            new_l=[]
            l2=l.replace("(","( ").replace(")"," )")
            if "push" not in l2 and "pop" not in l2 and "bv" not in l2 and "BitVec" not in l2:
                l2_split=l2.split(" ")
                for w in l2_split:
                    if w=="Int":
                        new_l.append("Real")
                    elif w.isdigit():
                        new_l.append(w+".0")
                    else:
                        new_l.append(w)
                temp_file.write(" ".join(new_l))
            else:
                temp_file.write(l2)
    temp_file.close()
    return input_file+"_temp"

def add_id_variables(commands_list,var_dict):
    id_c=0
    for (name,args) in commands_list:
        args_inner=args[1]
        print(args[0])
        expression_type=args[0].get_type()
        print(args[0],expression_type)
        #prendere il tipo dell'espressionie -> adesso parsati con bitvector
        if ":id" not in args_inner:
            var_id_name="opt_var_"+str(id_c)
            args_inner+=[":id",var_id_name]
            if "BV" in str(expression_type):
                var_dict[var_id_name]=[expression_type]
            else:
                var_dict[var_id_name]=["Real"]
            id_c+=1
        else:
            index=args_inner.index(":id")
            var_id_name=args_inner[index+1]
            if var_id_name not in [str(el) for el in var_dict.keys()]:
                if "BV" in str(expression_type):
                    var_dict[var_id_name]=[expression_type]
                else:
                    var_dict[var_id_name]=["Real"]
    return var_dict

def write_list_variables_lex(variables,file_out):
    
    #ret=write_list_variables(variables,file_out)
    bv_len=write_list_variables(variables,file_out)
    if bv_len!=0: #maybe change it to ==-1 to avoid to use lexicographic search
        raise BVtoLexicographic("BVintoLexicographic is not supported") #a meno che non si utilizzi toNum
    file_out.write("array[int] of var float: obj_array;\n")



def write_list_variables(variables,file_out):
    bv_len=0
    for var in variables.keys():
        #In minizinc if no domain is specified there can be problems with the solver like g12
        bv_search=re.search(r"BV{([0-9]+)}",str(variables[var][0]))
        if bv_search:
            bv_len,=bv_search.groups()
            file_out.write("array[1.."+bv_len+"] of var bool:"+str(var)+";\n")
        elif "Real" in str(variables[var][0]) and len(variables[var])!=2:
            file_out.write("var -2147483646.0..2147483646.0 : "+str(var)+";\n")
            #file_out.write("var float : "+str(var)+";\n")  
        elif len(variables[var])==2: #parameter declaration
            type,name=variables[var][0],variables[var][1]
            if "Real" in str(type): 
                type="float"
            file_out.write("par "+str(type).lower()+": "+str(var)+" = "+str(name)+";\n")
        elif len(variables[var])==1:
            type=variables[var][0]
            file_out.write("var "+str(type).lower()+":"+str(var)+";\n")
    return bv_len


def write_assertions(asserts_list,file_out,var_dict,bv_len): #the last parameter indicates the list of BV variables to be transformed
    #reference: https://github.com/hakank/hakank/blob/master/minizinc/bit_vector1.mzn
    #TODO: occhio al segno
    bv_len_int=int(bv_len)
    if bv_len!=0:
        file_out.write("function var int: toNum(array[1.."+str(bv_len)+"] of var bool: a) = -ceil(pow(2,"+str(bv_len)+"-1))*a[1]+"+"sum([ceil(pow(2,"+str(bv_len)+"-i)) * a[i]| i in 2.."+str(bv_len)+"]);\n")
    for el in asserts_list:
        el=re.sub(r"\(! (.*)\)",r"not(\1)",str(el))
        el=re.sub(r"\(!(.*)\)",r"not(\1)",str(el))
        assert_str = str(el).strip("[|]").replace("|","\/").replace("&","/\\")
        assert_str = re.sub("False","false",assert_str)
        assert_str = re.sub("True","true",assert_str)
        bv_search_l=re.findall(r"([0-9]+)_[0-9]+",assert_str) #anche da qui posso ricavarmi la lenght
        for bv_value_match in bv_search_l:
            bv_value=int(bv_value_match)
            if bv_value>pow(2,bv_len_int-1):
                bv_value-=pow(2,bv_len_int)
            assert_str = re.sub(""+bv_value_match+"_[0-9]+",str(bv_value),assert_str) #numbers BV - se sotto la meta di 2^bvlen-1 fai negativo
        assert_str = re.sub(r"s([<=,=>,<,>])",r"\1",assert_str) #relationship operators BV
        if bv_len!=0:
            for var in var_dict: #TODO:rivedi condizione
                    bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[var][0]))
                    if bv_search:
                        assert_str=re.sub(r"("+str(var)+")",r"toNum(\1)",assert_str)    
        file_out.write("constraint "+assert_str+";\n")

def write_assertions_soft(asserts_soft_list,file_out):
    #catch all the ones with the same id, then construct the constraint for the cost, name of variable equal to the id
    set_cost_variables = set([l[-1] for l in asserts_soft_list]) #one variable for each of them
    var_index = {name:0 for name in set_cost_variables}
    var_weight = {}
    '''
    Due to parsing problem, add initilly a variable for each id of assert soft
    for v in set_cost_variables:
        if flag:
            file_out.write("var float:"+v+";\n")
        else:
            file_out.write("var int:"+v+";\n")
    '''
    for el in asserts_soft_list:
        file_out.write("var bool:"+el[-1]+"_"+str(var_index[el[-1]])+";\n")
        el[0]=re.sub(r"\(! (.*)\)",r"not(\1)",str(el[0]))
        el[0] = re.sub("False","false",str(el[0]))
        el[0] = re.sub("True","true",str(el[0]))
        file_out.write("constraint ("+el[-1]+"_"+str(var_index[el[-1]])+"="+str(el[0])+");\n")
        var_weight[el[-1]+"_"+str(var_index[el[-1]])]=el[1]
        var_index[el[-1]]+=1
    for cost in set_cost_variables:
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

#TODO: aggiungere se ci sono bitvector per il lex e in caso lanciare un eccezione
def write_commands_lex(commands_list,file_out): #if 1 is real
    new_var_list=list()
    for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
        upper=None
        lower=None
        #taking the id value -> equal to the variable
        args_inner=args[1]
        index=args_inner.index(":id")
        new_var=args_inner[index+1] 
        new_var_list.append(new_var)
        if ":upper" in args_inner:
            index=args_inner.index(":upper")
            upper=args_inner[index+1]
        if ":lower" in args:
            index=args_inner.index(":lower")
            lower=args_inner[index+1]
        #if flag:
        #TODO:aggiungere casistica per i bitvector anche se non credo si possa implementare -> gestire il caso
        #file_out.write("var float: "+new_var+";\n")
        #else:
        #    file_out.write("var int: "+new_var+";\n")
        if name=="maximize":
            file_out.write("constraint ("+new_var+"=-("+str(args[0])+"));\n")
        else:
            file_out.write("constraint ("+new_var+"="+str(args[0])+");\n")
        if upper is not None:
            file_out.write("constraint ("+new_var+"<="+upper+");\n")
        if lower is not None:
            file_out.write("constraint ("+new_var+">="+lower+");\n")
    file_out.write("obj_array=[")
    file_out.write(new_var_list[0])
    for el in new_var_list[1:]:
        file_out.write(","+el)
    file_out.write("];\n")
    file_out.write("%use minisearch\n")
    file_out.write("solve search minimize_lex_float(obj_array);\n")
    ##PAPER Implementation
    file_out.write("""\n
function ann : minimize_lex_float(array[int] of var float : objs) =
    next () /\ commit () /\ print () /\\
    repeat(
        scope(
            post(lex_less(objs,[sol(objs[i]) | i in index_set (objs)])) /\\
            if next() then commit () /\ print () else break endif
    ));
""")


def write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,logic_name,out_file):
    file_out=open(out_file,"w")
    file_out.write("include \"globals.mzn\";\n")
    file_out.write("include \"minisearch.mzn\";\n")
    write_list_variables_lex(var_dict,file_out) 
    write_assertions(asserts_list,file_out,var_dict,0) #setting the bv_len=0 to be sure that to lexicographic for bitvector
    write_assertions_soft(asserts_soft_list,file_out)
    write_commands_lex(commands_list,file_out)
    file_out.close()

def write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
    #for each box new file
    #in commands_list only maximize and minimize
    '''
    add the constraint to keep track also to the other function to minimize or maximize
    they should be different
    '''
    i=0
    common_lines=[]
    unique_assign=[]
    for (name,args) in commands_list: #argslist [cost_function,[parameter]]
        upper=None
        lower=None
        args_inner=args[1]
        index=args_inner.index(":id")
        new_var=args_inner[index+1]
        #writing the maximize and the minimize
        if ":upper" in args_inner:
            index=args_inner.index(":upper")
            upper=str(args_inner[index+1])
        if ":lower" in args_inner:
            index=args_inner.index(":lower")
            lower=str(args_inner[index+1])
        unique_assign.append("constraint ("+new_var+"="+str(args[0])+");\n")
        if upper is not None:
            #lower=re.sub(r"([0-9]+)_[0-9]+",r"\1",lower) #numbers
            bv_search_l=re.findall(r"([0-9]+)_([0-9])+",upper) #anche da qui posso ricavarmi la lenght
            if len(bv_search_l)>0:
                for (bv_value_match,bv_len_int) in bv_search_l:
                    bv_value=int(bv_value_match)
                    bv_len_int=int(bv_len_int)
                    if bv_value>pow(2,bv_len_int-1):
                        bv_value-=pow(2,bv_len_int)
                    upper = re.sub(""+bv_value_match+"_[0-9]+",str(bv_value),upper)
                    common_lines.append("constraint (toNum("+new_var+")<="+upper+");\n")
            else:
                common_lines.append("constraint ("+new_var+"<="+upper+");\n")
        if lower is not None:
            #lower=re.sub(r"([0-9]+)_[0-9]+",r"\1",lower) #numbers
            bv_search_l=re.findall(r"([0-9]+)_([0-9])+",lower) #anche da qui posso ricavarmi la lenght
            if len(bv_search_l)>0:
                for (bv_value_match,bv_len_int) in bv_search_l:
                    bv_value=int(bv_value_match)
                    bv_len_int=int(bv_len_int)
                    if bv_value>pow(2,bv_len_int-1):
                        bv_value-=pow(2,bv_len_int)
                    lower = re.sub(""+bv_value_match+"_[0-9]+",str(bv_value),lower)
                    common_lines.append("constraint (toNum("+new_var+")>="+lower+");\n")
            else:
                common_lines.append("constraint ("+new_var+">="+lower+");\n")
    for (name,args) in commands_list:
        i+=1
        file_out=open(out_file.replace(".mzn","_b"+str(i))+".mzn","w")
        file_out.write("include \"globals.mzn\";\n")
        bv_len=write_list_variables(var_dict,file_out)
        write_assertions(asserts_list,file_out,var_dict,bv_len)
        write_assertions_soft(asserts_soft_list,file_out)
        file_out.write(unique_assign[i-1]) #same list as command_list
        for line in common_lines:
            file_out.write(line)
        args_inner=args[1]
        index=args_inner.index(":id")
        new_var=args_inner[index+1] 
        print(var_dict)
        if name=='maximize':
            bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[new_var][0]))
            if bv_search:
                bv_len,=bv_search.groups()
                file_out.write("solve maximize toNum("+new_var+");\n")
            else:
                file_out.write("solve maximize "+new_var+";\n")
        else:
            bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[new_var][0]))
            if bv_search:
                bv_len,=bv_search.groups()
                file_out.write("solve minimize toNum("+new_var+");\n")
            else:
                file_out.write("solve minimize "+new_var+";\n")
        file_out.close()

#considering the case to unroll the  stack
def write_stack(stack,logic_name,out_file):
    #check set-priority options -> looking for the last one
    flat_stack=[item for l in stack for item in l]
    var_dict={}
    asserts_list=[]
    asserts_soft_list=[]
    commands_list=[] #maximize/minimize
    set_priority_option="box" #default value for the case where no option is specified
    '''
    type_var, detect int or real -> the purpose is to determine the value of the id_opt_Variable, 
    one for each optimization command
    to review in case of BV
    the problem is that this information is retrived also somewhere else, so 
    it has to be decided which point is better to determine the type of the variable
    In any case, dobut about MixedInteger Optimization -> if everythin becames Real
    and one variable was Integer -> can the the result be different? Rounding
    '''
    #type_var="Real" 
    for el in flat_stack:
        if el.name=='declare-fun' and len(el.args)==1: #constant condition
            var_dict[str(el.args[0])]=[el.args[0].get_type()] #rescue all the variable type (float)
        elif el.name=='define-fun':
            #found_type=el.args[2]
            var_dict[str(el.args[0])]=[el.args[2],el.args[3]] #[type,value]
        elif el.name=='assert':
            asserts_list.append(el.args)
        elif el.name=='assert-soft':
            asserts_soft_list.append(el.args)
        elif el.name=='set-option' and el.args[0]==':opt.priority':  #keep the last one
            set_priority_option=el.args[1]
        elif el.name=='maximize' or el.name=='minimize':
            commands_list.append((el.name,el.args))
    var_dict=add_id_variables(commands_list,var_dict)
    if set_priority_option == 'lex': #lexicographic order 
        write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,logic_name,out_file)
    else: #box-  also the default one
        write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)

def parse_stack(commands,logic_name,out_file):
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
            write_stack(current_stack,logic_name,out_file.replace(".","_"+str(file_index)+"."))
            file_index+=1
        else:
            current_stack[-1].append(cmd)
        
               
def startParsing(input_file,out_file):
    parser = SmtLib20Parser() # We read the SMT-LIB Script by creating a Parser From here we can get the SMT-LIB script.
    #get_script_fnname execute the script using a file as source.
    new_input_f = pre_proc(input_file)
    script = parser.get_script_fname(new_input_f)
    commands = script.commands #getting the list of commands (set-option,set-logic,declaration,assert,command)
    commands_name = [cmd.name for cmd in commands]
    for el in commands:
        print el
    logic_name=""
    #logic_name=str([cmd.args[0] for cmd in commands if cmd.name=='set-logic'][0])
    parse_stack(commands,logic_name,out_file) #logic name is a not more used parameter
  
if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs("Incorrect number of arguments")
    else:
        startParsing(sys.argv[1],sys.argv[2])