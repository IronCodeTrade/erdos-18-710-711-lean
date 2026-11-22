import sys
sys.setrecursionlimit(100000)
def f(n):
    # match k=1..n into a in [n+1, n+L-1]; grow L
    match_a={}  # a -> k
    match_k={}
    def try_k(k,seen,hi):
        # multiples of k in [n+1,hi]
        a=((n)//k+1)*k
        while a<=hi:
            if a not in seen:
                seen.add(a)
                if a not in match_a or try_k(match_a[a],seen,hi):
                    match_a[a]=k; match_k[k]=a; return True
            a+=k
        return False
    L=n+1
    ks=list(range(n,0,-1))
    while True:
        hi=n+L-1
        ok=True
        for k in ks:
            if k in match_k: continue
            if not try_k(k,set(),hi): ok=False; break
        if ok: return L, dict(match_k)
        L+=1
if __name__=="__main__":
    N=int(sys.argv[1])
    for n in range(1,N+1):
        L,_=f(n); print(n,L,flush=True)
