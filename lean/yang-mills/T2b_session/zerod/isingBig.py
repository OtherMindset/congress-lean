import numpy as np, itertools,sys
rng=np.random.default_rng(int(sys.argv[1]))
worst={'E2':-np.inf,'IC':-np.inf}; cnt=0
SP={n:np.array(list(itertools.product([-1,1],repeat=n)),float) for n in range(3,13)}
import time; t0=time.time()
while time.time()-t0<95:
    n=int(rng.integers(3,13)); p=rng.random()
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<p); J=np.triu(J,1)*rng.choice([0.05,0.2,0.5,1,2]); J=J+J.T
    Sp=SP[n]; E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; M=Sp.sum(1)
    for H in [0.005,0.05,0.2,0.6,1.5,3.0]:
        cnt+=1
        lw=E0+H*M; w=np.exp(lw-lw.max()); w/=w.sum()
        Ex=lambda f:(w*f).sum(); Mc=M-Ex(M)
        i,j=rng.choice(n,2,replace=False); k,l=rng.choice(n,2)
        sk=Sp[:,k]; sij=Sp[:,i]*Sp[:,j]; skc=sk-Ex(sk); sijc=sij-Ex(sij)
        N=Ex(skc*sijc); D=Ex(Sp[:,l]); slc=Sp[:,l]-D
        if N>1e-8 and D>1e-8:
            v=(D*Ex(skc*sijc*Mc)-N*Ex(slc*Mc))/(N*D)
            if v>worst['E2']: worst['E2']=v; best=('E2',n,(i,j,k,l),H,v,N)
        B=list(rng.choice(n,rng.integers(2,n+1),replace=False)); MB=Sp[:,B].sum(1)
        a=MB-Ex(MB); a2=MB**2-Ex(MB**2); m=Ex(MB); c=Ex(a*a2)
        if c>1e-8 and m>1e-8:
            v=(Ex(a*a2*Mc)*m-c*Ex(a*Mc))/(c*m)
            if v>worst['IC']: worst['IC']=v; bestI=('IC',n,len(B),H,v,c)
print('tests',cnt); print(best); print(bestI)
