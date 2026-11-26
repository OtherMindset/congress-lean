from b3 import *
import itertools
STK=[(0,0,False),(0,0,True),(1,0,True),(0,1,True),(1,1,True)]
def check(n,J_,c,H):
    ed=[(a,b) for a in range(n) for b in range(a+1,n)]; J=[J_[e] for e in ed]
    E=ed+[(x,n) for x in range(n)]; Wt=list(J)+list(H*c)
    cw=[collapsed(w) for w in Wt]
    A={0,1,2,n}; num=0;Z=0;ZA=0
    for combo in itertools.product(range(5),repeat=len(E)):
        b1=[0]*(n+1);b2=[0]*(n+1);wt=1.0;adj={x:[] for x in range(n+1)}
        for e,s in enumerate(combo):
            k=STK[s];wt*=cw[e][k];u,v=E[e]
            if k[0]:b1[u]^=1;b1[v]^=1
            if k[1]:b2[u]^=1;b2[v]^=1
            if k[2]:adj[u].append(v);adj[v].append(u)
        if any(b2):continue
        bd={x for x in range(n+1) if b1[x]}
        if not bd: Z+=wt
        if bd==A:
            ZA+=wt;seen={0};st=[0]
            while st:
                u=st.pop()
                for v in adj[u]:
                    if v not in seen:seen.add(v);st.append(v)
            if A<=seen:num+=wt
    return num/ZA
n=4
ed=[(a,b) for a in range(n) for b in range(a+1,n)]
for t in range(3):
    Jd={e:rng.uniform(0.1,1) for e in ed}; c=rng.uniform(0,1.5,n); H=rng.uniform(0.2,1)
    S,w=spin_data(n,ed,[Jd[e] for e in ed],c,H)
    s=lambda *i: ev(w,np.prod(S[:,list(i)],axis=1))
    # sites 0,1,2 ; B={0,1,2}
    spin=(s(0)*s(1,2)+s(1)*s(0,2)+s(2)*s(0,1))/s(0,1,2)
    print(1+2*check(n,Jd,c,H),spin)
