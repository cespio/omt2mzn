'''
Francesco Contaldo 2018 
A python parser omt2mnz

Linear Arithmetic (Integer & Real) | QF_LIA QF_LRA
Non Linear Arithmetic  (Integer & Real) | QF_NIA QF_NRA
Set |
ArrayBit |

'''
from pysmt.smtlib.parser import *
import sys


class WrongNumbArgs(StandardError):
    pass
class NoLogicDefined(StandardError):
    pass


#function to parse LIA 
#TODO -> define also a sort of return
def write_list_variables(variables,file_out):
    for var in variables.keys():
        print(type(var))
        print(type((variables[var])))
        file_out.write("var "+variables[var]+":"+str(var))

    

def parseQF_LIA(commands,out_file):
    file_out=open(out_file,"w") #opening the output file -> maybe useful to use the with statement
    #looking for function, NB as function declaration
    dict_constant={}
    for el in commands:
        if el.name=='declare-fun' and len(el.args)==1: #constant condition
            dict_constant[el.args[0]]=el.args[0].get_type()
    write_list_variables(dict_constant,file_out)
    

def startParsing(input_file,out_file):
    parser = SmtLib20Parser() # We read the SMT-LIB Script by creating a Parser From here we can get the SMT-LIB script.
    #get_script_fnname execute the script using a file as source.
    script = parser.get_script_fname(sys.argv[1]) #The script element contains the structure of the parsed SMTLIBv2 file
    commands = script.commands #getting the list of commands (set-logic,declaration,assert,command)
    if commands[0].name!='set-logic': #checkign the logic of the smtlibv2 input file
        raise NoLogicDefined('No logic is defined')
    elif str(commands[0].args[0])=='QF_LIA': #linear integere program
            parseQF_LIA(commands[1:],out_file) #pushing out the command setlogic
    

if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs('Incorrect number of arguments')
    else:
        startParsing(sys.argv[1],sys.argv[2])
