import numpy as np, itertools,sys,time
rng=np.random.default_rng(int(sys.argv[1])); mode=sys.argv[2]
SP={n:np.array(list(itertools.product([-1,1],repeat=n)),float) for n in range(3,12)}
w1=np.inf; w2=np.inf; t0=time.time()
while time.time()-t0<45:
    n=int(rng.integers(3,12)); p=rng.random()
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<p); J=np.triu(J,1)*rng.choice([0.05,0.3,1,2]); J=J+J.T
    Sp=SP[n]; E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; D=Sp.sum(1)
    for H in [0.005,0.05,0.2,0.6,1.5]:
        lw=E0+H*D; w=np.exp(lw-lw.max()); w/=w.sum(); Ex=lambda f:(w*f).sum(); Dc=D-Ex(D)
        k,i,j=rng.choice(n,3,replace=False)
        F=Sp[:,k]*Sp[:,i]*Sp[:,j]; m=Ex(Sp[:,k]); N=Ex(F)
        if N>1e-8 and m>1e-8:
            v=(Ex((F-N)*Dc)*m-N*Ex((Sp[:,k]-m)*Dc))/(N*m)
            if v<w1: w1=v; b1=(n,H,v)
        # block version: B0, By disjoint or equal
        perm=rng.permutation(n); s0=rng.integers(1,n); B0=perm[:s0]
        By=B0 if rng.random()<0.5 else perm[s0:]
        if len(By)==0: continue
        M0=Sp[:,B0].sum(1); My=Sp[:,By].sum(1); F=M0*My**2; m=Ex(M0); N=Ex(F)
        if N>1e-8 and m>1e-8:
            v=(Ex((F-N)*Dc)*m-N*Ex((M0-m)*Dc))/(N*m)
            if v<w2: w2=v; b2=(n,len(B0),len(By),'same' if By is B0 else 'disj',H,v)
print('distinct k,i,j:',w1,b1); print('block <M0 My^2>/<M0>:',w2,b2)
