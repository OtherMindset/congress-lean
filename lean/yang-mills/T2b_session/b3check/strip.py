import numpy as np, itertools, sys
rng=np.random.default_rng(int(sys.argv[1]))
def P4strip(w,L,Jv,Jh,h,sites):
    # Jv[col][r] coupling (r,r+1) in column col; Jh[col][r] coupling (col,r)-(col+1,r); h[col][r]
    st=np.array(list(itertools.product([1,-1],repeat=w)),float); q=len(st)
    def colw(c):
        e=np.zeros(q)
        for r in range(w-1): e+=Jv[c][r]*st[:,r]*st[:,r+1]
        e+=st@h[c]; return np.exp(e)
    def T(c):
        e=np.zeros((q,q))
        for r in range(w): e+=Jh[c][r]*np.outer(st[:,r],st[:,r])
        return np.exp(e)
    def corr(S):  # S: list of (col,row)
        v=np.ones(q); lg=0
        for c in range(L):
            d=colw(c).copy()
            for (cc,r) in S:
                if cc==c: d=d*st[:,r]
            v=v*d
            if c<L-1: v=T(c)@v
            s=np.abs(v).max(); v/=s; lg+=np.log(s)
        return v.sum(),lg
    Z,lz=corr([]); res={}
    def m(S):
        x,l=corr(S); return x/Z*np.exp(l-lz)
    a,b,c=sites
    t3=m([a,b,c])
    return (m([a])*m([b,c])+m([b])*m([a,c])+m([c])*m([a,b]))/t3
worst=0;ex=None
for t in range(int(sys.argv[2])):
    w=int(rng.integers(2,5)); L=int(rng.integers(10,31))
    scale=10**rng.uniform(-1,0.1)
    Jv=rng.uniform(0,1,(L,w))*scale*rng.choice([0.2,1,1],(L,w)); Jh=rng.uniform(0,1,(L,w))*scale
    allp=[(cc,r) for cc in range(L) for r in range(w)]
    sites=[allp[i] for i in rng.choice(len(allp),3,replace=False)]
    if rng.random()<.5: sites=[(int(rng.integers(0,3)),int(rng.integers(0,w))),(int(rng.integers(0,L)),int(rng.integers(0,w))),(L-1-int(rng.integers(0,3)),int(rng.integers(0,w)))]
    if len(set(sites))<3: continue
    c=rng.random((L,w))*(rng.random((L,w))<.7)
    for s in sites: c[s]=1
    v=[P4strip(w,L,Jv,Jh,H*c,sites) for H in np.logspace(-1,1,25)]
    d=np.diff(v); 
    if -d.min()>worst: worst=-d.min();ex=(w,L,sites,scale)
print("strip ray worst decrease",worst,ex)
