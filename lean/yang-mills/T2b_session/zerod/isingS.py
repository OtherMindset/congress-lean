# Ising test: S(H)=<M_B;M_B^2>/<M_B>, uniform field on all sites; nonincreasing in H?
import numpy as np, itertools,sys
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def S_of(J,B,Hs,Sp):
    E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; M=Sp.sum(1); MB=Sp[:,B].sum(1)
    out=[]
    for H in Hs:
        lw=E0+H*M; w=np.exp(lw-lw.max()); w/=w.sum()
        m=(w*MB).sum(); m2=(w*MB**2).sum(); m3=(w*MB**3).sum()
        out.append((m3-m*m2)/m)
    return np.array(out)
worst=-np.inf; Hs=np.linspace(0.01,3,120)
for trial in range(4000):
    n=rng.integers(2,10); Sp=np.array(list(itertools.product([-1,1],repeat=n)),float)
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<rng.random()); J=np.triu(J,1)*rng.choice([0.1,0.5,1,2]); J=J+J.T
    k=rng.integers(1,n+1); B=list(rng.choice(n,k,replace=False))
    S=S_of(J,B,Hs,Sp); d=np.diff(S)/np.maximum(np.abs(S[:-1]),1e-9)
    if d.max()>worst: worst=d.max(); print(trial,n,B,round(worst,6),Hs[d.argmax()],flush=True); np.save('worstS.npy',J); 
