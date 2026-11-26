import numpy as np, itertools,sys,time
rng=np.random.default_rng(int(sys.argv[1]))
worst={}; best={}
SP={n:np.array(list(itertools.product([-1,1],repeat=n)),float) for n in range(3,12)}
def upd(name,v,info):
    if v>worst.get(name,-np.inf): worst[name]=v; best[name]=info
t0=time.time(); cnt=0
while time.time()-t0<95:
    n=int(rng.integers(3,12)); p=rng.random()
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<p); J=np.triu(J,1)*rng.choice([0.05,0.2,0.5,1,2]); J=J+J.T
    Sp=SP[n]; E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; M=Sp.sum(1)
    for H in [0.005,0.05,0.2,0.6,1.5,3.0]:
        cnt+=1
        lw=E0+H*M; w=np.exp(lw-lw.max()); w/=w.sum()
        Ex=lambda f:(w*f).sum(); Mc=M-Ex(M)
        i,j=rng.choice(n,2,replace=False); k=rng.integers(n)
        sk=Sp[:,k]; sij=Sp[:,i]*Sp[:,j]; skc=sk-Ex(sk); sijc=sij-Ex(sij)
        N=Ex(skc*sijc); D=Ex(sk)
        if N>1e-8 and D>1e-8: upd('E1(l=k)',(D*Ex(skc*sijc*Mc)-N*Ex(skc*Mc))/(N*D),(n,i,j,k,H))
        B=list(rng.choice(n,rng.integers(2,n+1),replace=False)); MB=Sp[:,B].sum(1)
        i,j=rng.choice(B,2,replace=False); a=MB-Ex(MB); m=Ex(MB)
        N=Ex(a*sijc if False else a*(Sp[:,i]*Sp[:,j]-Ex(Sp[:,i]*Sp[:,j])))
        if N>1e-8 and m>1e-8: upd('E3 <M_B;s_is_j>/<M_B>',(m*Ex(a*(Sp[:,i]*Sp[:,j]-Ex(Sp[:,i]*Sp[:,j]))*Mc)-N*Ex(a*Mc))/(N*m),(n,len(B),H))
        k=rng.integers(n); sk=Sp[:,k]; skc=sk-Ex(sk); a2=MB**2-Ex(MB**2); N=Ex(skc*a2); D=Ex(sk)
        if N>1e-8 and D>1e-8: upd('E4 <s_k;M_B^2>/<s_k>',(D*Ex(skc*a2*Mc)-N*Ex(skc*Mc))/(N*D),(n,len(B),k in B,H))
print(cnt)
for k in worst: print(k,worst[k],best[k])
