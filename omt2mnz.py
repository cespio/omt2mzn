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

def parseQF_LIA(commands,out_file):
    

def startParsing(input_file,out_file):
    # We read the SMT-LIB Script by creating a Parser From here we can get the SMT-LIB script.
    parser = SmtLib20Parser()
    '''
    See SmtLibParser.get_script_fname() if to pass the path of a file.
    '''
    #inside the script we should find the command to be parsed
    script = parser.get_script_fname(sys.argv[1])
    commands = script.commands
    print(script.)
    if commands[0].name!='set-logic':
        raise NoLogicDefined('No logic is defined')
    elif str(commands[0].args[0])=='QF_LIA':
            parseQF_LIA(commands,out_file)

if __name__ == "__main__":
    if len(sys.argv)!=3:
        raise WrongNumbArgs('Incorrect number of arguments')
    else:
        startParsing(sys.argv[1],sys.argv[2])
