import numpy as np, itertools,sys,time
rng=np.random.default_rng(int(sys.argv[1]))
SP={n:np.array(list(itertools.product([-1,1],repeat=n)),float) for n in range(3,12)}
worst=-np.inf; t0=time.time(); cnt=0
while time.time()-t0<90:
    n=int(rng.integers(3,12)); p=rng.random()
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<p); J=np.triu(J,1)*rng.choice([0.05,0.2,0.5,1,2]); J=J+J.T
    c=rng.exponential(1,n)*(rng.random(n)<0.7)
    if c.sum()==0: continue
    Sp=SP[n]; E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; D=Sp@c
    for H in [0.005,0.05,0.2,0.6,1.5]:
        cnt+=1; lw=E0+H*D; w=np.exp(lw-lw.max()); w/=w.sum(); Ex=lambda f:(w*f).sum(); Dc=D-Ex(D)
        B=list(rng.choice(n,rng.integers(2,n+1),replace=False)); MB=Sp[:,B].sum(1)
        a=MB-Ex(MB); a2=MB**2-Ex(MB**2); m=Ex(MB); cc=Ex(a*a2)
        if cc>1e-8 and m>1e-8:
            v=(Ex(a*a2*Dc)*m-cc*Ex(a*Dc))/(cc*m)
            if v>worst: worst=v; best=(n,len(B),H,v)
print(cnt,worst,best)
