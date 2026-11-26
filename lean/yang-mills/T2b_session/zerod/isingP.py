import numpy as np, itertools,sys
rng=np.random.default_rng(int(sys.argv[1])); nonunif=sys.argv[2]=='1'
worst={'P':-np.inf,'E2':-np.inf,'IC':-np.inf,'ICx':-np.inf}
for trial in range(2500):
    n=rng.integers(3,9); J=rng.exponential(1,(n,n))*(rng.random((n,n))<rng.random()); J=np.triu(J,1)*rng.choice([0.1,0.3,1,2]); J=J+J.T
    Sp=np.array(list(itertools.product([-1,1],repeat=n)),float)
    E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; M=Sp.sum(1)
    base=rng.exponential(1,n)*rng.choice([0.3,1]) if nonunif else np.zeros(n)
    H=rng.choice([0.02,0.1,0.4,1.0,2.0,4.0])
    lw=E0+Sp@base+H*M; w=np.exp(lw-lw.max()); w/=w.sum()
    Ex=lambda f:(w*f).sum(); Mc=M-Ex(M)
    i,j,k,l,x=rng.choice(n,5)
    if i==j: continue
    sk=Sp[:,k]; sij=Sp[:,i]*Sp[:,j]; skc=sk-Ex(sk); sijc=sij-Ex(sij)
    N=Ex(skc*sijc); D=Ex(Sp[:,l]); sx=Sp[:,x]-Ex(Sp[:,x]); slc=Sp[:,l]-D
    if N>1e-7 and D>1e-7:
        v=(D*Ex(skc*sijc*sx)-N*Ex(slc*sx))/(N*D)
        if v>worst['P']: worst['P']=v; print('P',trial,n,(i,j,k,l,x),H,v,flush=True)
        v=(D*Ex(skc*sijc*Mc)-N*Ex(slc*Mc))/(N*D)
        if v>worst['E2']: worst['E2']=v; print('E2',trial,n,(i,j,k,l),H,v,flush=True)
    B=list(rng.choice(n,rng.integers(2,n+1),replace=False)); MB=Sp[:,B].sum(1)
    a=MB-Ex(MB); a2=MB**2-Ex(MB**2); m=Ex(MB); c=Ex(a*a2)
    if c>1e-7 and m>1e-7:
        v=(Ex(a*a2*Mc)*m-c*Ex(a*Mc))/(c*m)
        if v>worst['IC']: worst['IC']=v; print('IC',trial,n,B,H,v,flush=True)
        v=(Ex(a*a2*sx)*m-c*Ex(a*sx))/(c*m)
        if v>worst['ICx']: worst['ICx']=v; print('ICx',trial,n,B,x,H,v,flush=True)
