import numpy as np, itertools, sys
from p4 import confs,P4
rng=np.random.default_rng(int(sys.argv[1]))
def run(kind,ntr,Nlo,Nhi,jr=(-1.5,0.7)):
    w=0;ex=None;rel=0
    for t in range(ntr):
        N=int(rng.integers(Nlo,Nhi+1)); conf=confs(N)
        J=np.triu(10**rng.uniform(*jr,(N,N))*(rng.random((N,N))<rng.uniform(.3,1)),1)
        Eb=np.einsum('ci,ij,cj->c',conf,J,conf)
        H0=10**rng.uniform(-1,0.5)
        c=rng.random(N)*(rng.random(N)<.8); c[:3]=1
        if kind=='ray':
            hs=[H*c for H in np.logspace(-1.5,1.3,50)]
            v=[P4(conf,Eb,h) for h in hs]
        else:
            h0=H0*c
            x=int(rng.integers(0,3)) if kind=='coordB' else int(rng.integers(3,N)) if N>3 else 3
            if x>=N: continue
            hs=[]
            for g in np.logspace(-1.5,1.3,50):
                h=h0.copy(); h[x]=g; hs.append(h)
            v=[P4(conf,Eb,h) for h in hs]
        d=np.diff(v); k=np.argmin(d)
        if -d[k]>w: w=-d[k];ex=(N,J.round(4).tolist(),c.round(4).tolist(),H0,x if kind!='ray' else None,k)
    return w,ex
kind=sys.argv[2]
w,ex=run(kind,int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]))
print(kind,"worst decrease",w)
if w>1e-9: print(ex)
