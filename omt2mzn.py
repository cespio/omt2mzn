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
#TODO: risolvere la questione di bitvector per le operazioni con il segno
#TODO: chiamre il toNum corretto a seconda della lunghezza
#TODO: BV o SBV
#TODO: completare il parsing
#TODO: inside the parser i first try to parse in SBV then BV
#TODO: self if
#TODO: define-fun come parametro viene esploso 
#TODO: per ifthenelse e stato modifica il walker di ite che printa direttamente in fzn
#expression link #b010101 puo compararire in var,par,assert,assert-soft,
'''
from pyomt.smtlib.parser import *
from pyomt.exceptions import *
import pyomt
import sys
import re


class WrongNumbArgs(StandardError):
    pass
class NoLogicDefined(StandardError): #TODO:no more used
    pass 
class BVtoLexicographic(StandardError): #TODO:no more used
    pass

def pre_proc(input_file):
    lines=open(input_file).readlines()
    temp_file=open(input_file+"_temp","w")
    nl=[] #new_lines
    set_declaration_id=set() #variable declaration for assert soft, make sure it is unique
    for l in lines:
        if l[0]!=";": #skipping comment line
            l=re.sub(r";.*","",l) #deleting comment in the same line
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
            nl.append(l)
            
    lines=nl
    for l in nl:
        l2=l.replace("(","( ").replace(")"," )")
        temp_file.write(l2)
    temp_file.close()
    return input_file+"_temp"

def modify_type_assert_soft(asserts_soft_list,var_dict):
    '''
        The variable here as been declared automatically Real, then
        it is necessary to check all its expression and try to understand its type
    '''
    dict_type={}
    for assert_exp in asserts_soft_list:
        #get id and type
        if assert_exp[1]==1:
            current_type="Int"
        else:
            current_type=assert_exp[1].get_type()
        if assert_exp[2] not in dict_type:
            dict_type[assert_exp[2]]=set()
            dict_type[assert_exp[2]].add(str(current_type))
        else:
            dict_type[assert_exp[2]].add(str(current_type))
    for k in dict_type:
        if len(dict_type[k])==1:
            var_dict[k]=dict_type[k][0]
        else:
            if "Real" in dict_type[k] and "Int" in dict_type[k]: #TODO: add the other cases
                var_dict[k]="Real"
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

def ifBV(string):
    bv_search_l=re.findall(r"([0-9]+)_([0-9])+",string) #anche da qui posso ricavarmi la lenght
    if len(bv_search_l)>0:
        for (bv_value_match,bv_len_int) in bv_search_l:
            bv_value=int(bv_value_match)
            bv_len_int=int(bv_len_int)
            if bv_value>pow(2,bv_len_int-1):
                bv_value-=pow(2,bv_len_int)
            string = re.sub(""+bv_value_match+"_[0-9]+",str(bv_value),string)  
    bv_search_l2=re.findall(r"#b([01]+)",string)
    #print(bv_search_l)
    #print(bv_search_l2)
    if len(bv_search_l2)>0:
        for match in bv_search_l2:
            x=int(match,2)    
            int_value=x - (1 << len(match))  
            string = re.sub("#b"+match,str(int_value),string) 
    return (len(bv_search_l2)+len(bv_search_l))>0,string

def retrieve_bv_lengths(var_dict):
    ret_list=[]
    for var in var_dict.keys():
        bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[var][0]))
        if bv_search:
            bv_len,=bv_search.groups()
            ret_list.append(bv_len)
    return ret_list

def write_list_variables(variables,file_out):
    bv_len=0
    for var in variables.keys():
        '''
        In minizinc if no domain is specified there can be problems with the solver like g12
        '''
        bv_search=re.search(r"BV{([0-9]+)}",str(variables[var][0]))
        if bv_search and len(variables[var])!=2: 
            bv_len,=bv_search.groups()
            file_out.write("array[1.."+bv_len+"] of var bool:"+str(var)+";\n")
        elif bv_search and len(variables[var])==2: #parameter condition
            #bv_len,=bv_search.groups() useless
            expr = str(variables[var][1])
            #two different kind of search -> two different type to express the bitvector
            bv_search_l=re.findall(r"([0-9]+)_([0-9])+",expr) #retrieve the length also from here
            if len(bv_search_l)>0:
                for (bv_value_match,bv_len_int) in bv_search_l:
                    bv_value=int(bv_value_match)
                    bv_len_int=int(bv_len_int)
                    if bv_value>pow(2,bv_len_int-1):
                        bv_value-=pow(2,bv_len_int)
                        expr = re.sub(""+bv_value_match+"_[0-9]+",str(bv_value),expr)
                
            bv_search_l2=re.findall(r"#b([01]+)",expr)
            if len(bv_search_l2)>0:
                for match in bv_search_l2:
                    int_value=int(match,2)    
                    #int_value=x - (1 << len(match)) avoid sign
                    expr = re.sub("#b"+match,str(int_value),expr)
            file_out.write("par int: "+str(var)+" = "+str(expr)+";\n")                 
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


def write_assertions(asserts_list,file_out,var_dict):
    #TODO: remove bvlen parameter -> we could have different length of bitvectos inside the same input
    #reference: https://github.com/hakank/hakank/blob/master/minizinc/bit_vector1.mzn
    #TODO: manage the sign
    #bv_len_list=retrieve_bv_lengths(var_dict)
    #for l in bv_len_list: #for each possible length declare a function of the same length
    #    file_out.write("function var int: toNumSigned"+str(l)+"(array[1.."+str(l)+"] of var bool: a) = -ceil(pow(2,"+str(bv_len)+"-1))*a[1]+"+"sum([ceil(pow(2,"+str(bv_len)+"-i)) * a[i]| i in 2.."+str(bv_len)+"]);\n")
    #    file_out.write("function var int: toNum"+str(l)+"(array[1.."+str(l)+"] of var bool: a) = sum([ceil(pow(2,"+str(bv_len)+"-i)) * a[i]| i in 1.."+str(bv_len)+"]);\n")
    for el in asserts_list:
        print(type(el))
        if type(el) is list:
            el=el[0]
        print("A")
        el=el.serialize()
        print("A1")
        #assert_str=re.sub(r"! (.*)",r"not(\1)",assert_str)
        #assert_str=re.sub(r"!(.*)",r"not(\1)",assert_str)
        assert_str=re.sub("!","not",str(el))
        print("B")
        assert_str = assert_str.strip("[|]").replace("|","\/").replace("&","/\\")
        print("C")
        assert_str = re.sub("False","false",assert_str)
        print("D")
        assert_str = re.sub("True","true",assert_str)
        print("E")
        assert_str = re.sub(r"ToReal([A-Za-z0-9]+)",r"\1",assert_str)
        print("F")
        #assert_str = re.sub(r"s([<=,=>,<,>])",r"\1",assert_str)#TODO: usare qui conversione con il segnosare qui conversione con il segno
        #assert_str = re.sub(r"u([<=,=>,<,>])",r"\1",assert_str)
        #bv_search_l=re.findall(r"([0-9]+)_[0-9]+",assert_str) #anche da qui posso ricavarmi la lenght
        '''
        for bv_value_match in bv_search_l:
            bv_value=int(bv_value_match)
            if bv_value>pow(2,bv_len_int-1):
                bv_value-=pow(2,bv_len_int)
            assert_str = re.sub(""+bv_value_match+"_[0-9]+",str(bv_value),assert_str) #numbers BV 
        '''
        '''
        if len(bv_len_list)!=0:
            for var in var_dict: #TODO:rivedi condizione
                    bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[var][0]))
                    if bv_search:
                        assert_str=re.sub(r"("+str(var)+")",r"toNum(\1)",assert_str)    
        '''
        file_out.write("constraint "+assert_str+";\n")

def write_assertions_soft(asserts_soft_list,file_out):
    #catch all the ones with the same id, then construct the constraint for the cost, name of variable equal to the id
    set_cost_variables = set([l[-1] for l in asserts_soft_list]) #one variable for each of them
    var_index = {name:0 for name in set_cost_variables}
    var_weight = {}
    for el in asserts_soft_list:
        file_out.write("var bool:"+el[-1]+"_"+str(var_index[el[-1]])+";\n")
        el[0]=re.sub(r"\(! (.*)\)",r"not(\1)",str(el[0]))
        el[0]=re.sub(r"\(!(.*)\)",r"not(\1)",str(el[0]))
        el[0] = re.sub("False","false",str(el[0]))
        el[0] = re.sub("True","true",str(el[0]))
        el[0] = re.sub(r"ToReal([A-Za-z0-9]+)",r"\1",str(el[0]))
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

def write_commands_lex(commands_list,var_dict,file_out):
    new_var_list=[]
    var_list_type=set() #if just one type rescued from the maximize,otherwise use to2float
    for (name,args) in commands_list: #only maximize or minimize -> manage the lower and the upper
        upper=None
        lower=None
        args_inner=args[1]
        index=args_inner.index(":id") #taking the id value -> equal to the variable
        new_var=args_inner[index+1]
        var_list_type.add(var_dict[new_var][0]) 
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
        #bv_search=re.search(r"BV{([0-9]+)}",str(var_dict[new_var][0]))
        if name=="maximize":
            file_out.write("constraint ("+new_var+"=-("+str(args[0])+"));\n")
        else:
            file_out.write("constraint ("+new_var+"="+str(args[0])+");\n")
        if upper is not None:
            file_out.write("constraint ("+new_var+"<="+upper+");\n")
        if lower is not None:
            file_out.write("constraint ("+new_var+">="+lower+");\n")
    #Assuming only float and int
    type=""
    if len(var_list_type)==0:
        type=var_list_type.pop()
    else:
        type="float"
        '''
        in this case is necessary to add the constraint to change what is int into real for the search
        for what is real
        '''
        new_var_list2=[]
        for var_name in new_var_list:
            if var_dict[var_name]=="Int" or var_dict[var_name]=="int":
                new_var_name=var_name+"_f"
                file_out.write("var float: "+new_var_name+";\n")
                file_out.write("constraint("+new_var_name+"=int2float("+var_name+"));\n")
                new_var_list2.append(new_var_name)
            else:
                new_var_list2.append(var_name)
        new_var_list=new_var_list2 #changing the list
    file_out.write("array[int] of var "+type+": obj_array;\n")  #TODO: modify to the type
    file_out.write("obj_array=[")
    file_out.write(new_var_list[0])
    for el in new_var_list[1:]:
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
        for each function to maximize or to minize create a new file,
        keep the assignement to the optimization variables on all the files but not the upper
        and lower constraints
    '''
    i=0
    common_lines=[]
    unique_lower=[]
    unique_upper=[]
    print("Inizio Primo loop di write_stack_box")
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
        common_lines.append("constraint ("+new_var+"="+str(args[0])+");\n")
        #TODO: rivedere qua gestione di toNUM
        if upper is not None:
            #upper=re.sub(r"([0-9]+)_[0-9]+",r"\1",upper) #numbers
            cond,upper=ifBV(upper)
            if cond:  
                unique_upper.append("constraint (toNum("+new_var+")<="+upper+");\n")
            else:
                unique_upper.append("constraint ("+new_var+"<="+upper+");\n")
        else:
            unique_lower.append("")
        if lower is not None:
            cond,lower=ifBV(lower)
            if cond:
                unique_lower.append("constraint (toNum("+new_var+")<="+lower+");\n")
            else:
                unique_lower.append("constraint ("+new_var+"<="+lower+");\n")
        else:
            unique_upper.append("")
    print("Fine primo loop di write_stack_box")
    print("Inizio secondo loop di write_stack_box")
    print(commands_list,len(commands_list))
    for (name,args) in commands_list:
        i+=1
        file_out=open(out_file.replace(".mzn","_b"+str(i))+".mzn","w")
        file_out.write("include \"globals.mzn\";\n")
        print("Inizio a scrivere le var")
        write_list_variables(var_dict,file_out)
        print("Fine scrivere le var")
        print("Inizio a scrivere le asserts")
        write_assertions(asserts_list,file_out,var_dict)
        print("Fine scrittura di asserts")
        write_assertions_soft(asserts_soft_list,file_out)
        for line in common_lines:
            file_out.write(line)
        
        file_out.write(unique_lower[i-1]) #same list as command_list
        file_out.write(unique_upper[i-1]) #same list as command_list
        args_inner=args[1]
        index=args_inner.index(":id")
        new_var=args_inner[index+1] 
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
    type_var, detect int or real -> the purpose is to determine the value of the id_opt_Variable, 
    one for each optimization command
    to review in case of BV
    '''
    flat_stack=[item for l in stack for item in l] #considering the case to unroll the  stack
    var_dict={}
    asserts_list=[]
    asserts_soft_list=[]
    commands_list=[] #maximize/minimize
    set_priority_option="box" #default value for the case where no option is specified, look for the last one in case
    for el in flat_stack:
        if el.name=='declare-fun' and len(el.args)==1: #constant condition
            var_dict[str(el.args[0])]=[el.args[0].get_type()] #rescue all the variable type
        elif el.name=='define-fun':
            #var_dict[str(el.args[0])]=[el.args[2],el.args[3]] #[type,value]
            pass
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
    if set_priority_option == 'lex': #lexicographic order 
        write_stack_lex(var_dict,asserts_list,asserts_soft_list,commands_list,out_file)
    else: #box-  also the default one
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
            print("calling write_stack")
            write_stack(current_stack,out_file.replace(".","_"+str(file_index)+"."))
            file_index+=1
        else:
            current_stack[-1].append(cmd)
        
               
def startParsing(input_file,out_file):
    # We read the SMT-LIB Script by creating a Parser From here we can get the SMT-LIB script.
    parser = SmtLib20Parser() 
    #get_script_fnname execute the script using a file as source.
    new_input_f = pre_proc(input_file)
    script = parser.get_script_fname(new_input_f)
    print("Parsing form pyomt is complete")
    commands = script.commands #getting the list of commands (set-option,set-logic,declaration,assert,command)
    #for cmd in commands: #print the list of parsed commands
    #    print cmd 
    parse_stack(commands,out_file) #calling the main function
  
if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs("Incorrect number of arguments")
    else:
        startParsing(sys.argv[1],sys.argv[2])