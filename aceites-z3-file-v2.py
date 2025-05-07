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

# K: mínimo número de aceites que se refinan por mes (longitud = meses)
K = list(map(int, input().split()))  # e.g. "5 0 3 2 0 5"

# T: mínimo toneladas por aceite refinado
T = int(input())  # e.g. "0"

# incomp: incompatibilidades, una línea por aceite en formato "{a,b,c}" o "{}"
incomp = []
for _ in range(aceites):
    raw = input().strip()
    vals = raw.strip('{} ')  # quita llaves
    if vals:
        incomp.append(set(map(int, vals.split(','))))
    else:
        incomp.append(set())

# afines: afinidades, una línea por aceite en formato "{a,b}" o "{}"
afinidad = []
for _ in range(aceites):
    raw = input().strip()
    vals = raw.strip('{} ')
    if vals:
        afinidad.append(set(map(int, vals.split(','))))
    else:
        afinidad.append(set())

# 3) (Opcional) Mostrar todo para verificar

#print("VALOR =", VALOR)
#print("dureza =", dureza)
#print("precios =")
#for row in precios:
#    print(" ", row)
#print("MAXV =", MAXV, "MAXN =", MAXN, "MCAP =", MCAP, "CA =", CA)
#print("MinD =", MinD, "MaxD =", MaxD, "MinB =", MinB)
#print("inicial =", inicial)
#print("PV =", PV)

#print("K =", K)
#print("T =", T)
#print("incompatiblidad =", incomp)
#print("afinidad =", afinidad)


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

# El beneficio obentido supera el minimo establecido
s.add(beneficio >= MinB)

# - Extensión 

# El producto debe hacerse con un mínimo de K aceites
for m in range (meses):
    minimo = Sum([bool2int(ventas[m][a] > 0) for a in range(aceites)])
    s.add_soft(minimo >= K[m])

# Si un mes usamos un cierto aceite, entonces debemos usar como mínimo T toneladas.
for m in range (meses):
    for a in range (aceites):
        s.add_soft(Implies(ventas[m][a] > 0, ventas[m][a] >= T))

# Si usamos el aceite ANV 1 o el aceite ANV 2 en un cierto mes, entonces no podemos usar 
# ni el VEG 2ni el ANV3ese mes. Generalizad esta restriccion a que haya aceites incompatibles.
for m in range(meses):
    for a1 in range(aceites):
        # construimos la conjunción de ventas[m][a2] == 0 para cada a2 incompatible
        incompatibles = [ventas[m][a2] == 0 for a2 in incomp[a1]]
        # si no hay incompatibles, no añadimos restricción extra
        if incompatibles:
            s.add_soft(
                Implies(ventas[m][a1] > 0, And(*incompatibles)))

# Si usamos el aceite ANV 3 entonces debemos usar VEG 1 ese mes. Generalizad esta restriccion 
# a que haya aceites que requieren otros en su fabricacion.
for m in range(meses):
    for a1 in range(aceites):
        # construimos la conjunción de ventas[m][a2] > 0 para cada a2 requerido
        afines = [ventas[m][a2] > 0 for a2 in afinidad[a1]]
        # si no hay requisitos, no añadimos nada
        if afines:
            s.add_soft(Implies(ventas[m][a1] > 0, And(*afines)))

#Optimización

# minimizar el núumero de aceites usados cada mes.
for m in range(meses):
    for a in range(aceites):
        s.add_soft(ventas[m][a] == 0)

# Maximizar el beneficio 
# s.maximize(beneficio)

result = s.check()

print(result)

# Impresión de resultados
if s.check() == sat:
    model = s.model()
    # Construir matrices de resultados
    mat_c = [[model[compras[m][a]].as_long() for m in range(meses)] for a in range(aceites)]
    mat_e = [[model[almacen[m][a]].as_long() for m in range(meses)] for a in range(aceites)]
    mat_v = [[model[ventas[m][a]].as_long() for m in range(meses)] for a in range(aceites)]

    # Cabecera meses
    header = ['Mes '+str(m+1) for m in range(meses)]
    def print_section(name, matrix):
        print(f"\n{name}")
        print("".ljust(12), end="")
        for h in header: print(h.ljust(10), end="")
        print()
        for i,row in enumerate(matrix):
            print(f"Aceite {i+1}".ljust(12), end="")
            for val in row: print(str(val).ljust(10), end="")
            print()
    # Tablas Compras, Existencias, Ventas
    print_section('Compras', mat_c)
    print_section('Almecén', mat_e)
    print_section('Ventas', mat_v)

    # Durezas promedio por mes
    durezas_avg = []
    for m in range(meses):
        total = sum(mat_v[a][m] for a in range(aceites))
        if total>0:
            durezas_avg.append(sum(dureza[a]*mat_v[a][m] for a in range(aceites))/total)
        else:
            durezas_avg.append(0.0)
    print("\nDureza promedio")
    print("".ljust(12), end="")
    for h in header: print(h.ljust(10), end="")
    print()
    print("".ljust(12), end="")
    for d in durezas_avg: print(f"{d:.2f}".ljust(10), end="")
    print()

    # Existencias finales por aceite
    exist_final = []
    for a in range(aceites):
        exist_final.append(mat_e[a][meses-1] + mat_c[a][meses-1] - mat_v[a][meses-1])
    print("\nExistencias finales")
    print("".ljust(12), end="")
    for i in range(aceites): print(f"Aceite {i+1}".ljust(10), end="")
    print()
    print("".ljust(12), end="")
    for ef in exist_final: print(str(ef).ljust(10), end="")
    print(f"\n\nBeneficio total: {model[beneficio].as_long()}")
else:
    print("No se encontró solución óptima.")