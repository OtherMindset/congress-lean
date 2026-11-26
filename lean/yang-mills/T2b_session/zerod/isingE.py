# Elementary tests: T = <s_k; s_i s_j>/<s_l>, derivative along uniform field direction; fields may be nonuniform h_x>=0
import numpy as np, itertools,sys
rng=np.random.default_rng(int(sys.argv[1])); nonunif=sys.argv[2]=='1'
worst={'E1':-np.inf,'E2':-np.inf,'IC':-np.inf}
for trial in range(1500):
    n=rng.integers(3,9); J=rng.exponential(1,(n,n))*(rng.random((n,n))<rng.random()); J=np.triu(J,1)*rng.choice([0.1,0.3,1]); J=J+J.T
    Sp=np.array(list(itertools.product([-1,1],repeat=n)),float)
    E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; M=Sp.sum(1)
    base=rng.exponential(1,n)*rng.choice([0,0.3,1]) if nonunif else np.zeros(n)
    H=rng.choice([0.02,0.1,0.4,1.0,2.0])
    lw=E0+Sp@base+H*M; w=np.exp(lw-lw.max()); w/=w.sum()
    Ex=lambda f:(w*f).sum(); Mc=M-Ex(M)
    i,j,k,l=rng.choice(n,4,replace=n<4) if n>=4 else rng.choice(n,4)
    if i==j: continue
    sk=Sp[:,k]; sij=Sp[:,i]*Sp[:,j]; skc=sk-Ex(sk); sijc=sij-Ex(sij)
    N=Ex(skc*sijc); dN=Ex(skc*sijc*Mc)
    for name,ll in [('E1',k),('E2',l)]:
        D=Ex(Sp[:,ll]); dD=Ex((Sp[:,ll]-D)*Mc)
        if N<1e-9 or D<1e-9: continue
        v=(dN*D-N*dD)/(N*D)   # relative derivative of N/D
        if v>worst[name]: worst[name]=v; print(name,trial,n,(i,j,k,l),H,v,'N',N,flush=True)
    B=list(rng.choice(n,rng.integers(2,n+1),replace=False)); MB=Sp[:,B].sum(1)
    a=MB-Ex(MB); a2=MB**2-Ex(MB**2); m=Ex(MB); c=Ex(a*a2)
    if c>1e-9:
        v=(Ex(a*a2*Mc)*m-c*Ex(a*Mc))/(c*m)
        if v>worst['IC']: worst['IC']=v; print('IC',trial,n,B,H,v,flush=True)
