#!/usr/bin/env python

import re
import sys
fin=sys.argv[1]
with open(fin,"r") as inputf:
    for line in inputf:
        line=line.strip()
        if "constraint" not in line: 
            line1=re.sub(r"let|{|}|in |in$|;","",line)
            line2=re.sub(r"^(tmp_[0-9]+)\)",r"} in \1)",line1)
            if len(line2)!=1:
                line3=re.sub(r"$",r";",line2)
            else:
                line3=line2
            print(line3)
        else:
            print(line)
