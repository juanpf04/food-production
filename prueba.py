#!/usr/bin/python3
from z3 import *

import io  
import sys

filenameIn = sys.argv[1]
myinput = "".join(open(filenameIn, "r").readlines())
sys.stdin = io.StringIO(myinput)

# altura : altura de la torre
# disp : piezas disponibles
# Colores: Azul = 0, Rojo = 1 , Verde = 2;


entry = input().split()

vals = []
for i in range(len(entry)):
    vals.append(int(entry[i]))

def addexists(a):
    if len(a) == 0:
        return False
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return Or(x,addexists(a)) 

################################
# generamos un fichero smtlib2
################################

s = SolverFor("QF_LIA")

val = Int("val")

s.add(val >= 0)
s.add(val <= 2)

res = []
for i in range(len(vals)):
   res.append(val == vals[i])

s.add(Or(res))

result = s.check()
print(s.assertions())
print(result)


# print(s.model())
if result == sat:
    m = s.model()
    print(m[val])

#print(s.to_smt2())
exit(0)
