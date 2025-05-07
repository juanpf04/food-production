#!/usr/bin/python3
from z3 import *

import sys
import io

filenameIn = sys.argv[1]
myinput = "".join(open(filenameIn, "r").readlines())
sys.stdin = io.StringIO(myinput)

# - Variables de entrada --------------------------------------------------

VALOR = int(input())

meses = 6
nMeses = ["enero", "febrero", "marzo", "abril", "mayo", "junio"]
aceites = 5
nAceites = ["VEG1", "VEG2", "ANV1", "ANV2", "ANV3"]
vegs = 2

dureza = list(map(float, input().split()))

precios = []
for i in range(aceites+1):
    precios.append(list(map(int, input().split())))

MAXV = int(input())
MAXN = int(input())
MCAP = int(input())
CA   = int(input())

MinD = float(input())
MaxD = float(input())
MinB = int(input())

inicial = list(map(int, input().split()))

PV = int(input())

# -------------------------------------------------------------------------

# - Funciones -------------------------------------------------------------

def nCompras(m, a):
    return "compras_"+str(m)+"_"+str(a)

def nAlmacen(m, a):
    return "almacen_"+str(m)+"_"+str(a)

def nVentas(m, a):
    return "ventas_"+str(m)+"_"+str(a)

def bool2int(b):
    return If(b, 1, 0)

# -------------------------------------------------------------------------

# s = Solver()
s = Optimize()

# - Variables de salida ---------------------------------------------------

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

# -------------------------------------------------------------------------

# - Asserts ---------------------------------------------------------------

assert VALOR > 0, "El precio de venta (VALOR) debe ser positivo"

assert MAXV >= 0 and MAXN >= 0, "Las cantidades máximas de refinado (MAXV, MAXN) deben ser >= 0"

assert MCAP >= 0, "La capacidad máxima de almacenamiento (MCAP) debe ser >= 0"

assert CA >= 0, "El coste de almacenamiento por tonelada (CA) debe ser >= 0"

assert 0 <= MinD <= MaxD, "El intervalo de dureza (MinD, MaxD) debe cumplir 0 <= MinD <= MaxD"

assert 0 <= PV, "El porcentaje de variación (PV) debe ser >= 0"

assert MinB >= 0, "El beneficio mínimo (MinB) debe ser >= 0"

assert all(p >= 0 for row in precios for p in row), "El precio de cada aceite en cada mes debe ser >= 0"

assert all(d >= 0.0 for d in dureza), "La dureza de cada tipo de aceite debe ser >= 0.0"

# -------------------------------------------------------------------------

# - Restricciones ---------------------------------------------------------

for m in range(meses):
    for a in range (aceites):
        s.add(0 <= compras[m][a])
        s.add(compras[m][a] <= MCAP)

for m in range(meses):
    for a in range (aceites):
        s.add(0 <= almacen[m][a])
        s.add(almacen[m][a] <= MCAP)

cap_vegs = min(MCAP, MAXV)
cap_anvs = min(MCAP, MAXN)
for m in range(meses):
    for a in range(aceites):
        s.add(0 <= ventas[m][a])
        s.add(ventas[m][a] <= If(a < vegs, cap_vegs, cap_anvs))

# Nunca se refina mas del máximo permitido para cada tipo de aceite
for m in range(meses):
    ref_vegs = []
    ref_anvs = []

    for a in range(vegs):
        ref_vegs.append(ventas[m][a])
    for a in range(vegs, aceites):
        ref_anvs.append(ventas[m][a])

    s.add(Sum(ref_vegs) <= MAXV)
    s.add(Sum(ref_anvs) <= MAXN)


# Las Ei del primer mes son las iniciales del periodo
for a in range (aceites):
    s.add(almacen[0][a] == inicial[a])

# El resto de meses las Ei son Ef del mes anterior, que se obtienen con la siguiente formula: Ei + Compras = Ef + Ventas
for m in range (1, meses):
    for a in range (aceites):
        s.add(almacen[m - 1][a] + compras[m - 1][a] == almacen[m][a] + ventas[m - 1][a])

#Las Ei más las Compras de un mes no pueden superar el MCAP ya que no cabrían en el almacén
for m in range(meses):
    for a in range (aceites):
        s.add(almacen[m][a] + compras[m][a] <= MCAP)

# En caso de que se usen aceites NO vegetales, la dureza final debe estar entre MinD y MaxD
for m in range (meses):
    ref_anvs = []
    durezas = []
    ref_aceites = []

    for a in range(vegs, aceites):
        ref_anvs.append(ventas[m][a])

    for a in range(aceites):
        durezas.append(ventas[m][a] * dureza[a])
        ref_aceites.append(ventas[m][a])
   
    s.add(Implies(Sum(ref_anvs) > 0, And(Sum(durezas) >= MinD * Sum(ref_aceites), Sum(durezas) <= MaxD * Sum(ref_aceites))))

# Las Ef del último mes no varían más de PV de las Ei del periodo
for a in range (aceites):
    variacion = inicial[a] * PV // 100
    Ef = almacen[meses - 1][a] + compras[meses - 1][a] - ventas[meses - 1][a]

    s.add(inicial[a] - variacion <= Ef)
    s.add(Ef <= inicial[a] + variacion)

# El beneficio total se obtiene de las ventas - las compras - los costes de almacenamiento
b = []
for m in range(meses):
    for a in range (aceites):
        b.append(ventas[m][a] * VALOR - compras[m][a] * precios[m][a] - almacen[m][a] * CA)
        
s.add(beneficio == Sum(b))

# El beneficio obentido supera el minimo establecido. 
s.add(beneficio >= MinB)

# -------------------------------------------------------------------------

# - Optimización ----------------------------------------------------------

# Minimizar el número de aceites usados cada mes.
for m in range(meses):
    for a in range(aceites):
        s.add_soft(ventas[m][a] == 0)

# -------------------------------------------------------------------------

result = s.check()

print(result)

if result == sat:
    model = s.model()
    
    mat_c = [[model[compras[m][a]].as_long() for m in range(meses)] for a in range(aceites)]
    mat_a = [[model[almacen[m][a]].as_long() for m in range(meses)] for a in range(aceites)]
    mat_v = [[model[ventas[m][a]].as_long() for m in range(meses)] for a in range(aceites)]

    def print_section(name, matrix):
        print(f"\n{name}")
        print("".ljust(8), end="")
        for m in nMeses: print(m.ljust(10), end="")
        print()
        for i,row in enumerate(matrix):
            print(nAceites[i].ljust(8), end="")
            for val in row: print(str(val).ljust(10), end="")
            print()

    print_section('Compras', mat_c)
    print_section('Almacén', mat_a)
    print_section('Ventas', mat_v)

    print("\nDureza promedio")
    print("".ljust(8), end="")
    for m in nMeses: print(m.ljust(10), end="")
    print("\n".ljust(9), end="")
    for m in range(meses):
        total = sum(mat_v[a][m] for a in range(aceites))
        if total > 0:
            print(f"{sum(dureza[a]*mat_v[a][m] for a in range(aceites))/total:.2f}".ljust(10), end="")
        else:
            print("0.00".ljust(10), end="")


    print("\n\nExistencias finales")
    for a in range(aceites): 
        print(nAceites[a].ljust(8), end="")
        print(mat_a[a][meses-1] + mat_c[a][meses-1] - mat_v[a][meses-1])

    print(f"\nBeneficio total: {model[beneficio].as_long()}")
