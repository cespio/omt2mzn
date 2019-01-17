#!/usr/bin/env python3

import re
import sys
fin=sys.argv[1]
with open(fin,"r") as inputf:
    flagC=0
    for line in inputf:
        line=line.strip()
        match = None
        #print (line)
        compile_re = re.compile(r".*(\(([0-9]+.0) / ([0-9]+.0)\)).*")
        match = re.match(compile_re,line)
        if match is not None:
            #print(line)
            #print(match.groups(0))
            n,d = float(match.groups(0)[1]),float(match.groups(0)[2])
            r = n/d
            #print(r)
            line=re.sub(r""+match.groups(0)[0],str(r),line)
            #print(line)

        if "constraint" in line and "let" in line:
            flagC=1
            line1=line.replace("} in","")
            print(line1)
        elif re.match(r"tmp_[0-9]+\);",line) is not None:
            print("} in "+line)
            #pass
        else:
            print(line.replace("let {","").replace("} in",""))
            #pass