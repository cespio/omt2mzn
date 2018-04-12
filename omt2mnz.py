'''
Francesco Contaldo 2018 
A python parser omt2mnz

Linear Arithmetic (Integer & Real) | QF_LIA QF_LRA
Non Linear Arithmetic  (Integer & Real) | QF_NIA QF_NRA
Set |
ArrayBit |

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
            temp=re.sub(r"Int",r"Real",l)
            temp_file.write(re.sub(r"([0-9]+)",r"\1.0",temp))
    else:
        for l in lines:
            temp_file.write(l)
    temp_file.close()
    return input_file+"_temp"          
    

#function to parse LIA 
def write_list_variables(variables,file_out):
    for var in variables.keys():
        file_out.write("var "+str(variables[var]).lower().replace("Real","float")+":"+str(var)+";\n")

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
        print(el)
    write_list_variables(constants_dict,file_out)
    write_assertions(asserts_list,file_out)
    write_commands(commands_dict,file_out)
    

def startParsing(input_file,out_file):
    parser = SmtLib20Parser() # We read the SMT-LIB Script by creating a Parser From here we can get the SMT-LIB script.
    #get_script_fnname execute the script using a file as source.
    new_input_f = int2float(input_file)
    script = parser.get_script_fname(new_input_f)
    commands = script.commands #getting the list of commands (set-logic,declaration,assert,command)
    if commands[0].name!="set-logic": #checkign the logic of the smtlibv2 input file
        raise NoLogicDefined("No logic is defined")
    elif str(commands[0].args[0]) in ["QF_LIA","QF_LRA","QF_LIRA"] : #linear integere program
            parseQF_linear(commands[1:],out_file) #pushing out the command setlogic
  
if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs("Incorrect number of arguments")
    else:
        startParsing(sys.argv[1],sys.argv[2])
