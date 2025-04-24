#!/usr/bin/python3
from z3 import *

import sys
import io

# 1) Redirige todo el contenido del archivo de entrada a stdin
filenameIn = sys.argv[1]
with open(filenameIn, "r") as f:
    myinput = f.read()
sys.stdin = io.StringIO(myinput)

# 2) Lectura de variables
VALOR = int(input())

dureza = list(map(float, input().split()))

# Leemos 6 filas de precios, cada una con 5 enteros
precios = [list(map(int, input().split())) for _ in range(6)]

MAXV = int(input())
MAXN = int(input())
MCAP = int(input())
CA   = int(input())

MinD = float(input())
MaxD = float(input())
MinB = int(input())

inicial = list(map(int, input().split()))

PV = int(input())

# 3) (Opcional) Mostrar todo para verificar

print("VALOR =", VALOR)
print("dureza =", dureza)
print("precios =")
for row in precios:
    print(" ", row)
print("MAXV =", MAXV, "MAXN =", MAXN, "MCAP =", MCAP, "CA =", CA)
print("MinD =", MinD, "MaxD =", MaxD, "MinB =", MinB)
print("inicial =", inicial)
print("PV =", PV)
