import sys, math
from sympy import divisors
n=int(sys.argv[1]); m=math.factorial(n)
D=divisors(m); M=(1<<m)-1
C=int(sys.argv[2]) if len(sys.argv)>2 else 12
L=[1]*(C+1)
for d in D:
    for j in range(C,0,-1):
        L[j] |= (L[j-1]<<d)&M
# h = smallest c with L[c]==M
h=next(c for c in range(C+1) if L[c]==M)
x=L[h-1]
# first k with bit 0 in L[h-1]
inv=(~x)&M
k0=(inv & -inv).bit_length()-1
print(f"n={n} m={m} ndiv={len(D)} h={h} k0={k0}")
