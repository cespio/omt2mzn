'''
Francesco Contaldo 2018 
A python parser omt2mnz

Linear Arithmetic (Integer & Real) | QF_LIA QF_LRA
Non Linear Arithmetic  (Integer & Real) | QF_NIA QF_NRA
Set |
ArrayBit |


TODO:
- verificare opzioni di set-opt option
- aggiungere parsing opzioni di di minimize/maximize
-

'''
from pyomt.smtlib.parser import *
from pyomt.exceptions import *
import sys
import re


class WrongNumbArgs(StandardError):
    pass
class NoLogicDefined(StandardError):
    pass

def int2float(input_file):
    lines=open(input_file).readlines()
    temp_file=open(input_file+"_temp","w")
    flagReal=1
    for l in lines:
        if "declare-fun" in l and "Real" in l:
            flagReal=1
            break
    if flagReal==1:
        for l in lines:
            new_l=[]
            for w in l.strip().split(" "):
                if w=="Int":
                    new_l.append("Real")
                elif w.isdigit():
                    new_l.append("0."+w)
                else:
                    new_l.append(w)
            temp_file.write(" ".join(new_l))
            '''
            temp=re.sub(r"Int",r"Real",l)
            temp1=re.sub(r"([0-9]+)",r"\1.0",temp)
            temp_file.write(re.sub(r"([0-9]+)\.0\.([0-9]+)\.0",r"\1.\2",temp1))
            '''
    else:
        for l in lines:
            temp_file.write(l)
    temp_file.close()
    return input_file+"_temp"          
    

#function to parse LIA 
def write_list_variables(variables,file_out):
    for var in variables.keys():
        if "Real" in str(variables[var]):
            file_out.write("var -2147483646.0..2147483646.0 : "+str(var)+";\n") #se non hanno dominio lo esplicitio
            #problema con g12 number out of limitis, anche altrisolver come gecode mi davano lo stesso problema
        else:
            file_out.write("var "+str(variables[var]).lower()+":"+str(var)+";\n")

def write_assertions(asserts_list,file_out):
    for el in asserts_list:
        assert_str = str(el).strip("[|]").replace("|","\/").replace("&","/\\")
        file_out.write("constraint "+assert_str+";\n")

#the use of a dictionary can lead to a wrong sort of the command
#NB -> minizinc allows only one solve instruction at time
def write_commands(commands_dict,file_out):
    for comm in commands_dict:
        if comm=='check-sat':
            if 'maximize' in commands_dict or 'minimize' in commands_dict:
                file_out.write("")
            else:
                file_out.write("solve satisfability;\n")
        if comm=='maximize':
            file_out.write("solve maximize "+commands_dict[comm]+";\n")
        if comm=='minimize':
            file_out.write("solve minimize "+commands_dict[comm]+";\n")


def parseQF_linear(commands,out_file):
    file_out=open(out_file,"w") #opening the output file -> maybe useful to use the with statement
    #looking for function, NB as function declaration
    constants_dict={}
    asserts_list=[]
    commands_dict={}
    for el in commands:
        if el.name=='declare-fun' and len(el.args)==1: #constant condition
            constants_dict[el.args[0]]=el.args[0].get_type()
        elif el.name=='assert':
            asserts_list.append(el.args)
        else:
            commands_dict[el.name]=el.args
    write_list_variables(constants_dict,file_out)
    write_assertions(asserts_list,file_out)
    write_commands(commands_dict,file_out)
    file_out.close()
    

def startParsing(input_file,out_file):
    parser = SmtLib20Parser() # We read the SMT-LIB Script by creating a Parser From here we can get the SMT-LIB script.
    #get_script_fnname execute the script using a file as source.
    new_input_f = int2float(input_file)
    script = parser.get_script_fname(new_input_f)
    commands = script.commands #getting the list of commands (set-option,set-logic,declaration,assert,command)
    commands_name = [cmd.name for cmd in commands]
    for el in commands:
        print el
    if "set-logic" not in commands_name: #checkin the logic of the smtlibv2 input file
        raise NoLogicDefined("No logic is defined")
    else:
        logic_name=str([cmd.args[0] for cmd in commands if cmd.name=='set-logic'][0])
        if logic_name in ["QF_LIA","QF_LRA","QF_LIRA"] : #linear integer program
            parseQF_linear(commands,out_file)
  
if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs("Incorrect number of arguments")
    else:
        startParsing(sys.argv[1],sys.argv[2])
