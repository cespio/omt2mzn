'''
Francesco Contaldo 2018 
A python parser omt2mnz

Linear Arithmetic (Integer & Real) | QF_LIA QF_LRA
Non Linear Arithmetic  (Integer & Real) | QF_NIA QF_NRA
Set |
ArrayBit |

Define function as parameter
Declare function as var

Minisearch solo per int e non real
TODO:
- verificare opzioni di set-opt option
- floating point parser
- parsing di maximize e minimize con id inseriti
- lexicographic per QF_BV non dovrebbe essere implementabile, a me no che non si usi tonum
- #self.walk(f, threshold=9999999999999999999) printers.py l45

'''
from pyomt.smtlib.parser import *
from pyomt.exceptions import *
import sys
import re


class WrongNumbArgs(StandardError):
    pass
class NoLogicDefined(StandardError):
    pass

def preproc(input_file):
    lines=open(input_file).readlines()
    temp_file=open(input_file+"_temp","w")
    flagReal=0
    flagBV=0 #TODO: add comment to highlight the presence of the bitvector
    nl=[]
    set_declaration_id=set()
    for l in lines:
        if l[0]!=";":
            l=re.sub(r";.*","",l)
            if "declare-fun" in l and "Real" in l:
                flagReal=1
            #looking for bitvector to convert
            if "assert-soft" in l:
                if ":id " in l:
                    new_var = l.split(":id")[-1].strip().replace(")","")
                else:
                    new_var = "I"
                if new_var not in set_declaration_id:
                    nl.append("\n;declaration of additional variable for assert-soft\n")
                    nl.append("\n(declare-fun "+new_var+" () Int)\n")
                    set_declaration_id.add(new_var)
            bv_search=re.search(r"\(\(\_ to\_bv ([0-9]+)\) ([0-9]+)\)",l)
            if bv_search:
                (a1,a2)=bv_search.groups()
                bv=str('{0:0'+a1+'b}').format(int(a2))        
                l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) ([0-9]+)\)","#b"+bv,l)
            bv_search=re.search(r"\(\(\_ to\_bv ([0-9]+)\) \(- ([0-9]+)\)\)",l)
            if bv_search:
                (a1,a2)=bv_search.groups()
                bv=str('{0:0'+str(int(a1)-1)+'b}').format(int(a2))
                l=re.sub(r"\(\(\_ to\_bv ([0-9]+)\) \(- ([0-9]+)\)\)","#b1"+bv,l)
            
            nl.append(l)
    lines=nl    
    if flagReal==1:
        for l in nl:
            new_l=[]
            l2=l.replace("(","( ").replace(")"," )")
            if "push" not in l2 and "pop" not in l2:
                for w in l2.split(" "):
                    if w=="Int":
                        new_l.append("Real")
                    elif w.isdigit():
                        new_l.append(w+".0")
                    else:
                        new_l.append(w)
                temp_file.write(" ".join(new_l))
            else:
                temp_file.write(l2)
            '''
            temp=re.sub(r"Int",r"Real",l)
            temp1=re.sub(r"([0-9]+)",r"\1.0",temp)
            temp_file.write(re.sub(r"([0-9]+)\.0\.([0-9]+)\.0",r"\1.\2",temp1))
            '''
    else:
        for l in nl:
            temp_file.write(l)
    temp_file.close()
    return input_file+"_temp"          

def write_list_variables_lex(variables,file_out):
    ret=write_list_variables(variables,file_out)
    if ret:
        file_out.write("array[float] of var float: obj_array;\n")
    else:
        file_out.write("array[int] of var int: obj_array;\n")
    return ret

#specialize for BV variables creation
def write_list_variables_BV(variables,file_out):
    #TODO: how to declare a parameter?  
    for var in variables.keys(): #variable definition
        bv_search=re.search(r"BV{([0-9]+)}",str(variables[var][0]))
        if bv_search:
            bv_len,=bv_search.groups()
            file_out.write("array[1.."+bv_len+"] of var 0..1:"+str(var)+";\n")
    return bv_len

#return 1 if one of the variables is real
def write_list_variables(variables,file_out):
    ret=0
    for var in variables.keys():
        #In minizinc if no domain is specified there can be problems with the solver like g12
        if "Real" in str(variables[var][0]) and len(variables[var])!=2:
            #file_out.write("var -2147483646.0..2147483646.0 : "+str(var)+";\n")
            file_out.write("var float : "+str(var)+";\n")  
            ret=1
        elif len(variables[var])==2: #parameter declaration
            type,name=variables[var][0],variables[var][1]
            if "Real" in str(type): 
                type="float"
            file_out.write("par "+str(type).lower()+": "+str(var)+" = "+str(name)+";\n")
        elif len(variables[var])==1:
            type=variables[var][0]
            file_out.write("var "+str(type).lower()+":"+str(var)+";\n")
    return ret 

#TODO: parte di asset-soft BV, passing her variables_dict.keys()

def write_assertions_BV(asserts_list,file_out,list_var,bv_len): #the last parameter indicates the list of BV variables to be transformed
    #reference: https://github.com/hakank/hakank/blob/master/minizinc/bit_vector1.mzn
    #TODO: occhio al segno
    bv_len_int=bv_len
    file_out.write("function var int: toNum(array[1.."+str(bv_len_int)+"] of var int: a) = sum([ceil(pow(2,"+str(bv_len_int)+"-i)) * a[i]| i in 1.."+str(bv_len_int)+"]);\n")
    for el in asserts_list:
        el=re.sub(r"\(! (.*)\)",r"not(\1)",str(el))
        el=re.sub(r"\(!(.*)\)",r"not(\1)",str(el))
        assert_str = str(el).strip("[|]").replace("|","\/").replace("&","/\\")
        assert_str = re.sub(r"([0-9]+)_[0-9]+",r"\1",assert_str) #numbers
        assert_str = re.sub(r"s([<=,=>,<,>])",r"\1",assert_str) #relationship operators
        for var in list_var:
            assert_str=re.sub(r"("+str(var)+")",r"toNum(\1)",assert_str)
        file_out.write("constraint "+assert_str+";\n")


def write_assertions(asserts_list,file_out):
    for el in asserts_list:
        el=re.sub(r"\(! (.*)\)",r"not(\1)",str(el))
        el=re.sub(r"\(!(.*)\)",r"not(\1)",str(el))
        assert_str = str(el).strip("[|]").replace("|","\/").replace("&","/\\")
        file_out.write("constraint "+assert_str+";\n")

def write_assertions_soft(asserts_soft_list,file_out,flag):
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

def write_commands_lex(commands_list,flag,file_out): #if 1 is real
    new_var_list=[]
    var_name="temp_"
    print(commands_list)
    for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
        upper=None
        lower=None
        new_var = var_name+str(len(new_var_list)+1)
        new_var_list.append(new_var)
        args_inner=args[1]
        if ":upper" in args_inner:
            index=args_inner.index(":upper")
            upper=args_inner[index+1]
        if ":lower" in args:
            index=args_inner.index(":lower")
            lower=args_inner[index+1]
        if flag:
            file_out.write("var float: "+new_var+";\n")
        else:
            file_out.write("var int: "+new_var+";\n")
        if name=="maximize":
            file_out.write("constraint ("+new_var+"=-("+str(args[0])+"));\n")
        else:
            file_out.write("constraint ("+new_var+"="+str(args[0])+");\n")
        if upper is not None:
            file_out.write("constraint ("+new_var+"<="+upper+");\n")
        if lower is not None:
            file_out.write("constraint ("+new_var+">="+lower+");\n")
    file_out.write("obj_array=[")
    print(new_var_list)
    file_out.write(new_var_list[0])
    for el in new_var_list[1:]:
        file_out.write(","+el)
    file_out.write("];\n")
    file_out.write("%use minisearch\n")
    file_out.write("solve search minimize_lex(obj_array);\n")


def write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,logic_name,out_file):
    file_out=open(out_file,"w")
    file_out.write("include \"minisearch.mzn\";\n")
    flag=write_list_variables_lex(var_dict,file_out) #flag for the type of the variables
    write_assertions(asserts_list,file_out)
    write_assertions_soft(asserts_soft_list,file_out,flag)
    #flag for the type of the variables
    write_commands_lex(commands_list,flag,file_out)
    file_out.close()

def write_stack_box_BV(var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
    i=0
    new_var="obj_temp_var"
    for (name,args) in commands_list:
        upper=None
        lower=None
        file_out=open(out_file.replace(".mzn","_b"+str(i))+".mzn","w")
        i+=1
        bv_len=write_list_variables_BV(var_dict,file_out)
        file_out.write("array[1.."+str(bv_len)+"] of var 0..1:"+new_var+";\n")
        write_assertions_BV(asserts_list,file_out,var_dict.keys(),bv_len)
        #write_assertions_soft(asserts_soft_list,file_out,flag)
        #writing the maximize and the minimize
        args_inner=args[1]
        if ":upper" in args_inner:
            index=args_inner.index(":upper")
            upper=args_inner[index+1]
        if ":lower" in args:
            index=args_inner.index(":lower")
            lower=args_inner[index+1]
        file_out.write("constraint ("+new_var+"="+str(args[0])+");\n")
        if upper is not None:
            upper=re.sub(r"([0-9]+)_[0-9]+",r"\1",upper) #numbers
            file_out.write("constraint ("+new_var+"<="+upper+");\n")
        if lower is not None:
            lower=re.sub(r"([0-9]+)_[0-9]+",r"\1",lower) #numbers
            file_out.write("constraint ("+new_var+">="+lower+");\n")
        if name=='maximize':
            file_out.write("solve maximize toNum("+new_var+");\n")
        else:
            file_out.write("solve minimize toNum("+new_var+");\n")
        file_out.close()

def write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file):
    #for each box new file
    #in commands_list only maximize and minimize
    i=0
    new_var="obj_temp_var"
    for (name,args) in commands_list:
        upper=None
        lower=None
        file_out=open(out_file.replace(".mzn","_b"+str(i))+".mzn","w")
        i+=1
        flag=write_list_variables(var_dict,file_out)
        if flag:
            file_out.write("var float:"+new_var+";\n")
        else:
            file_out.write("var int:"+new_var+";\n")
        write_assertions(asserts_list,file_out)
        write_assertions_soft(asserts_soft_list,file_out,flag)
        #writing the maximize and the minimize
        args_inner=args[1]
        if ":upper" in args_inner:
            index=args_inner.index(":upper")
            upper=args_inner[index+1]
        if ":lower" in args:
            index=args_inner.index(":lower")
            lower=args_inner[index+1]
        file_out.write("constraint ("+new_var+"="+str(args[0])+");\n")
        if upper is not None:
            file_out.write("constraint ("+new_var+"<="+upper+");\n")
        if lower is not None:
            file_out.write("constraint ("+new_var+">="+lower+");\n")
        if name=='maximize':
            file_out.write("solve maximize "+new_var+";\n")
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
    for el in flat_stack:
        if el.name=='declare-fun' and len(el.args)==1: #constant condition
            var_dict[el.args[0]]=[el.args[0].get_type()]
        elif el.name=='define-fun':
            var_dict[el.args[0]]=[el.args[2],el.args[3]] #[type,value]
        elif el.name=='assert':
            asserts_list.append(el.args)
        elif el.name=='assert-soft':
            asserts_soft_list.append(el.args)
        elif el.name=='set-option' and el.args[0]==':opt.priority':  #keep the last one
            set_priority_option=el.args[1]
        elif el.name=='maximize' or el.name=='minimize':
            commands_list.append((el.name,el.args))
    if set_priority_option == 'lex': #lexicographic order 
        write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,logic_name,out_file)
    elif set_priority_option == 'box': #boxed different files
        if logic_name=="QF_BV":
            write_stack_box_BV(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)
        else:
            write_stack_box(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)

#TODO: modificare, passare la logica di interesse come parametro
def parse_stack(commands,logic_name,out_file):

    #creo lo stack, appena becco un checksat faccio il printout considerando anche set-option box/lex
    '''
    constructing the data structures
    consideration: looking for set-options, they imply different behaviour
    lex -> use minisearch different cost and constraint constructions
    box -> different file, one for each model

    Possible idea on how to manage push/pop and multiple opt.priority
    generate differente output file for each "section" that is present in the input file
    
    set model is used/mandatory only after boxed optimization (independent model for each objective)
    '''
    #stack approach, is it useful use this approach?
    #keep indexes for the objective
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
    new_input_f = preproc(input_file)
    script = parser.get_script_fname(new_input_f)
    commands = script.commands #getting the list of commands (set-option,set-logic,declaration,assert,command)
    commands_name = [cmd.name for cmd in commands]
    for el in commands:
        print el
    if "set-logic" not in commands_name: #checkin the logic of the smtlibv2 input file
        raise NoLogicDefined("No logic is defined")
    else:
        logic_name=str([cmd.args[0] for cmd in commands if cmd.name=='set-logic'][0])
        if logic_name in ["QF_LIA","QF_LRA","QF_LIRA","QF_BV"] : #linear integer program
            parse_stack(commands,logic_name,out_file)
    
  
if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs("Incorrect number of arguments")
    else:
        startParsing(sys.argv[1],sys.argv[2])
