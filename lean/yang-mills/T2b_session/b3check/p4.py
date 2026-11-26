import numpy as np, itertools, sys
rng=np.random.default_rng(0)
def confs(N): return np.array(list(itertools.product([1,-1],repeat=N)),float)
def P4(conf,Eb,h,s=(0,1,2)):
    E=Eb+conf@h; p=np.exp(E-E.max()); p/=p.sum()
    a,b,c=[conf[:,i] for i in s]
    m=lambda F:(p*F).sum()
    t3=m(a*b*c)
    return (m(a)*m(b*c)+m(b)*m(a*c)+m(c)*m(a*b))/t3
def worst(mode,ntr,Nlo,Nhi,jr=(-1.5,0.6),hr=(-3,1.3),dense=0.6):
    w=0;ex=None;cnt=0
    for t in range(ntr):
        N=int(rng.integers(Nlo,Nhi+1)); conf=confs(N)
        J=np.triu(10**rng.uniform(*jr,(N,N))*(rng.random((N,N))<dense),1)
        Eb=np.einsum('ci,ij,cj->c',conf,J,conf)
        hb=rng.random(N)*(rng.random(N)<.8)*10**rng.uniform(-2,0.5)
        grid=np.logspace(*hr,60)
        if mode=='ray':
            v=[P4(conf,Eb,H*hb) for H in grid]
        else:
            x=int(rng.integers(0,N)) if mode=='coord' else int(rng.integers(0,3))
            if mode=='coord3': pass
            v=[]
            for g in grid:
                h=hb.copy(); h[x]=g; v.append(P4(conf,Eb,h))
        dec=-np.min(np.diff(v)); cnt+=1
        if dec>w: w=dec;ex=(N,J,hb,(x if mode!='ray' else None))
    return w,ex
if __name__=="__main__":
    mode=sys.argv[1]
    w,ex=worst(mode,int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]))
    print(mode,"max decrease between grid points:",w)
    if w>1e-12: print(ex)
