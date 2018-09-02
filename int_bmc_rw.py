#!/usr/bin/env python

import re
import sys
fin=sys.argv[1]
with open(fin,"r") as inputf:
    for line in inputf:
        line=line.strip()
        if "constraint" in line and "let" in line:
            line1=re.sub("let{","",line)
            line1=re.sub("} in","\n",line1)
            line1=re.sub(r"constraint \(",r"constraint ( let { ",line1)
            line1=re.sub(r"\)\n",");\n",line1)
            line1=re.sub(r" (tmp_[0-9]+)\)",r" } in \1)",line1)
            print(line1)
        else:
            print(line)
