import sys
from f710 import f
def hall(n,K):
    # interval a in (n, n+K): [n+1, n+K-1]; returns (S,T) Hall violator, assuming no perfect matching
    hi=n+K-1
    match_a={}; match_k={}
    def adj(k):
        a=(n//k+1)*k
        while a<=hi: yield a; a+=k
    def try_k(k,seen):
        for a in adj(k):
            if a not in seen:
                seen.add(a)
                if a not in match_a or try_k(match_a[a],seen):
                    match_a[a]=k; match_k[k]=a; return True
        return False
    free=None
    for k in range(n,0,-1):
        if not try_k(k,set()): free=k; break
    assert free is not None
    # alternating BFS from free
    S={free}; T=set(); stack=[free]
    while stack:
        k=stack.pop()
        for a in adj(k):
            if a not in T:
                T.add(a)
                k2=match_a.get(a)
                assert k2 is not None
                if k2 not in S: S.add(k2); stack.append(k2)
    # verify: N(S) subset T, |T|<|S|
    for k in S:
        for a in adj(k): assert a in T
    assert len(T)<len(S)
    return sorted(S),sorted(T)
def check_upper(n,K,b):
    assert len(b)==n and len(set(b))==n
    for i in range(1,n+1): assert n<b[i-1]<n+K and b[i-1]%i==0
N=int(sys.argv[1])
import json
out=[]
for n in range(1,N+1):
    K,m=f(n)
    b=[m[i] for i in range(1,n+1)]
    check_upper(n,K,b)
    S,T=hall(n,K-1)
    out.append((n,K,b,S,T))
json.dump(out,open(f"cert_{N}.json","w"))
print("ok",N,[o[1] for o in out][-5:], max(len(o[3]) for o in out))
