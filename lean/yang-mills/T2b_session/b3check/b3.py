import numpy as np, itertools, math, sys
rng=np.random.default_rng(1)

# ---------- exact spin enumeration ----------
def spin_data(n,edges,J,c,H):
    S=np.array(list(itertools.product([1,-1],repeat=n)))
    E=np.zeros(len(S))
    for (a,b),j in zip(edges,J): E+=j*S[:,a]*S[:,b]
    E+=H*(S@c)
    w=np.exp(E); w/=w.sum()
    return S,w
def ev(w,F): return (w*F).sum()
def spin_IC(n,edges,J,c,H,B):
    S,w=spin_data(n,edges,J,c,H)
    M=S[:,B].sum(1).astype(float); C=S@c
    m1,m2,m3=[ev(w,M**p) for p in (1,2,3)]
    d=lambda F:ev(w,F*C)-ev(w,F)*ev(w,C)
    T=m3-m1*m2
    dT=d(M**3)-d(M)*m2-m1*d(M**2)
    dlogS=dT/T-d(M)/m1       # d/dH log S
    return T/m1,dlogS,S,w
def cov(w,F,G): return ev(w,F*G)-ev(w,F)*ev(w,G)

# ---------- identity 1 by direct truncated double-current enumeration (n=2,3) ----------
def trunc_check(n,edges,J,wg,T,k,i,j):
    # vertices 0..n-1, ghost n. edge list incl ghost
    E=list(edges)+[(x,n) for x in range(n)]; W=list(J)+list(wg)
    ne=len(E)
    fac=np.array([math.factorial(a) for a in range(T+1)],float)
    # per-edge arrays w^a/a!
    cnt=np.arange(T+1)
    A=set([k,n]) ^ set([i,j])
    def parity_vec(src):
        return src
    # enumerate all single currents with parity pattern: weight and parity-of-degree vector -> index by (boundary bitmask)
    # we need connectivity of n1+n2 support, so enumerate pairs per edge as (a,b) grid -> too big; use (T+1)^(2*ne) only for ne<=6 with small T via per-edge state collapse by (a%2,b%2,a+b>0)
    # direct per-edge sum over a,b in 0..T gives state weights; collapse is exact in the limit T->inf
    st={}
    for e,(u,v),wt in zip(range(ne),E,W):
        d={}
        for a in range(T+1):
            for b in range(T+1):
                key=(a%2,b%2,a+b>0); d[key]=d.get(key,0)+wt**(a+b)/(fac[a]*fac[b])
        st[e]=d
    keys=list(st[0].keys())
    num=0.0;ZA=0.0;Z0=0.0
    for combo in itertools.product(keys,repeat=ne):
        b1=[0]*(n+1);b2=[0]*(n+1);wt=1.0
        adj={x:[] for x in range(n+1)}
        for e,s in enumerate(combo):
            u,v=E[e]; wt*=st[e][s]
            if s[0]: b1[u]^=1;b1[v]^=1
            if s[1]: b2[u]^=1;b2[v]^=1
            if s[2]: adj[u].append(v);adj[v].append(u)
        if any(b2): continue
        bd=set(x for x in range(n+1) if b1[x])
        if bd==set():
            Z0+=wt
        if bd==A:
            ZA+=wt
            # connectivity k to g
            seen={k};stack=[k]
            while stack:
                u=stack.pop()
                for v in adj[u]:
                    if v not in seen: seen.add(v);stack.append(v)
            if n not in seen: num+=wt
    return num,ZA,Z0

def collapsed(Jv):
    c,s=np.cosh(Jv),np.sinh(Jv)
    return {(0,0,False):1.0,(0,0,True):c*c-1,(1,0,True):s*c,(0,1,True):s*c,(1,1,True):s*s}
