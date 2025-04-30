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

meses = 6
aceites = 5
vegs = 2

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

def nCompras(m, a):
    return "compras_"+str(m)+"_"+str(a)

def nAlmacen(m, a):
    return "almacen_"+str(m)+"_"+str(a)

def nVentas(m, a):
    return "ventas_"+str(m)+"_"+str(a)

def bool2int(b):
    return If(b, 1, 0)

s = Optimize()
# s = Solver()


compras = []
for m in range(meses):
    compras_mes = []
    for a in range (aceites):
        compras_mes.append(Int(nCompras(m, a)))
    compras.append(compras_mes)

almacen = []
for m in range(meses):
    almacen_mes = []
    for a in range (aceites):
        almacen_mes.append(Int(nAlmacen(m, a)))
    almacen.append(almacen_mes)

ventas = []
for m in range(meses):
    ventas_mes = []
    for a in range (aceites):
        ventas_mes.append(Int(nVentas(m, a)))
    ventas.append(ventas_mes)

beneficio = Int("beneficio")


for m in range(meses):
    for a in range (aceites):
        s.add(0 <= compras[m][a])
        s.add(compras[m][a] <= MCAP)

for m in range(meses):
    for a in range (aceites):
        s.add(0 <= almacen[m][a])
        s.add(almacen[m][a] <= MCAP)

for m in range(meses):
    for a in range (aceites):
        s.add(0 <= ventas[m][a])
        s.add(ventas[m][a] <= MCAP)


# posibles asserts TODO preguntar si hay que hacerlos

# Nunca se refina mas del máximo permitido para cada tipo de aceite
for m in range(meses):
    vegetales = Sum([ventas[m][a] for a in range(vegs)])
    s.add(vegetales <= MAXV)
    noVegatales = Sum([ventas[m][a] for a in range(vegs, aceites)])
    s.add(noVegatales <= MAXN)


# Las Ei del primer mes son las iniciales del periodo
for a in range (aceites):
    s.add(almacen[m][a] == inicial[a])

# El resto de meses las Ei son Ef del mes anterior, que se obtienen con la siguiente formula: Ei + Compras = Ef + Ventas
for m in range (1, meses):
    for a in range (aceites):
        s.add(almacen[m - 1][a] + compras[m - 1][a] == almacen[m][a] + ventas[m][a])

#Las Ei más las Compras de un mes no pueden superar el MCAP ya que no cabrían en el almacén
for m in range(meses):
    for a in range (aceites):
        s.add(almacen[m][a] + compras[m][a] <= MCAP)

# En caso de que se usen aceites NO vegetales, la dureza final debe estar entre MinD y MaxD
for m in range (meses):
    # (sum(a in anvs) (ventas[m, a])
    total_mes = Sum([ventas[m][a] for a in range(vegs, aceites)])
    # sum(a in aceites) (dureza[a] * ventas[m, a])
    suma_dureza = Sum([dureza[a] * ventas[m][a] for a in range (aceites)])
    # sum(a in aceites) (ventas[m, a])
    total_aceites = Sum([ventas[m][a] for a in range (aceites)])

    cond = Implies(
        total_mes > 0,
        And(
            suma_dureza >= MinD * total_aceites,
            suma_dureza <= MaxD * total_aceites
        )
    )
    s.add(cond)

# Las Ef del último mes no varían más de PV de las Ei del periodo
for a in range (aceites):
    variacion = inicial[a] * PV / 100
    final_ultimo_mes = almacen[meses - 1][a] + compras[meses - 1][a] - ventas[meses - 1][a]
    s.add(inicial[a] - variacion <= final_ultimo_mes)
    s.add(final_ultimo_mes <= inicial[a] + variacion)

# El beneficio total se obtiene de las ventas - las compras - los costes de almacenamiento
b = []
for m in range(meses):
    for a in range (aceites):
        b.append(ventas[m][a] * VALOR - compras[m][a] * precios[m][a] - almacen[m][a] * CA)
        
s.add(beneficio == Sum(b))

# El beneficio obentido supera el minimo establecido. 
s.add(beneficio >= MinB)

# Maximizar el beneficio 
s.maximize(beneficio)

result = s.check()

print(result)

if result == sat:
    m = s.model()
    print(m.eval(beneficio))

