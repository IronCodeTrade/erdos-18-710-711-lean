import sys, math, json
def adjf(n,m,K):
    hi=m+K-1
    def adj(k):
        a=(m//k+1)*k
        while a<=hi: yield a; a+=k
    return adj
def matching(n,m,K):
    adj=adjf(n,m,K); match_a={}; match_k={}
    def tk(k,seen):
        for a in adj(k):
            if a not in seen:
                seen.add(a)
                if a not in match_a or tk(match_a[a],seen):
                    match_a[a]=k; match_k[k]=a; return True
        return False
    for k in range(n,0,-1):
        if not tk(k,set()): return None,(k,match_a,adj)
    return [match_k[i] for i in range(1,n+1)],None
def hall(n,m,K):
    b,info=matching(n,m,K); assert b is None
    free,match_a,adj=info
    S={free};T=set();st=[free]
    while st:
        k=st.pop()
        for a in adj(k):
            if a not in T:
                T.add(a); k2=match_a[a]
                if k2 not in S: S.add(k2); st.append(k2)
    for k in S:
        for a in adj(k): assert a in T
    assert len(T)<len(S); return sorted(S),sorted(T)
if __name__!="__main__": pass
elif sys.argv[1]=="up":
    n=int(sys.argv[2]); P=math.lcm(*range(1,n+1)); K=2*n-1
    cs=[]
    for r in range(P):
        b,_=matching(n,r,K); assert b is not None, r
        assert len(set(b))==n and all(r<b[i-1]<r+K and b[i-1]%i==0 for i in range(1,n+1))
        cs.append(b)
    json.dump(cs,open(f"up_{n}.json","w")); print(n,P,"ok")
else:
    n,m,K=map(int,sys.argv[2:5]); print(json.dumps(hall(n,m,K)))
