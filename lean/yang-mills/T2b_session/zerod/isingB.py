# Ising analogue of (B): h -> <s0 si sj>/<s0> nondecreasing under uniform field (also nonuniform base fields / ray profiles)
import numpy as np, itertools,sys,time
rng=np.random.default_rng(int(sys.argv[1])); mode=sys.argv[2]
SP={n:np.array(list(itertools.product([-1,1],repeat=n)),float) for n in range(3,12)}
worst=np.inf; t0=time.time(); cnt=0
while time.time()-t0<50:
    n=int(rng.integers(3,12)); p=rng.random()
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<p); J=np.triu(J,1)*rng.choice([0.05,0.3,1,2]); J=J+J.T
    Sp=SP[n]; E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2
    c=np.ones(n) if mode=='unif' else rng.exponential(1,n)*(rng.random(n)<0.7)
    base=rng.exponential(1,n)*0.5 if mode=='base' else np.zeros(n)
    D=Sp@c
    for H in [0.005,0.05,0.2,0.6,1.5]:
        cnt+=1; lw=E0+H*D+Sp@base; w=np.exp(lw-lw.max()); w/=w.sum(); Ex=lambda f:(w*f).sum(); Dc=D-Ex(D)
        i,j=rng.choice(n,2,replace=False); k=rng.integers(n)
        F=Sp[:,k]*Sp[:,i]*Sp[:,j]; m=Ex(Sp[:,k]); N=Ex(F)
        if abs(N)>1e-8 and m>1e-8:
            v=(Ex((F-N)*Dc)*m-N*Ex((Sp[:,k]-m)*Dc))/(abs(N)*m)*np.sign(N)
            if v<worst: worst=v; best=(n,(k,i,j),H,v,N)
print(mode,cnt,'min rel derivative',worst,best)
