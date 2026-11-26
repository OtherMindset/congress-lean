# Check Psi(v)=E0[sum_x (phi_x+phi'_x)(phi_x-phi'_x)^2 | M+M'=v]/v monotone (zero field), block-Ising rings (translation invariant)
import numpy as np, itertools, sys
def run(N,L,cw,Jn,verbose=False):
    n=N*L; S=np.array(list(itertools.product([-1,1],repeat=n)),float)
    blk=S.reshape(len(S),L,N).sum(2)           # phi_x (unscaled)
    E=cw/N*0.5*((blk**2).sum(1)-N*L*0)        # CW intra: (cw/2N)(sum)^2 up to const
    for x in range(L):
        if L>1 and (L>2 or x==0): E=E+Jn/N*blk[:,x]*blk[:,(x+1)%L]
    w=np.exp(E-E.max()); w/=w.sum(); M=blk.sum(1)
    # pairs
    Mv=np.add.outer(M,M).ravel(); W=np.outer(w,w).ravel()
    F=np.zeros_like(Mv)
    for x in range(L):
        a=np.add.outer(blk[:,x],blk[:,x]).ravel(); d=np.subtract.outer(blk[:,x],blk[:,x]).ravel()
        F+=a*d**2
    vals=np.unique(Mv[Mv>0]); psi=[]
    for v in vals:
        msk=Mv==v; psi.append((W[msk]*F[msk]).sum()/W[msk].sum()/v)
    psi=np.array(psi); return vals,psi
rng=np.random.default_rng(0); worst=-np.inf
for (N,L) in [(2,2),(3,2),(4,2),(2,3),(3,3),(2,4),(5,2),(2,5),(4,3),(3,4),(6,2),(2,6)]:
    for t in range(6):
        cw=rng.uniform(0.2,2.5); Jn=rng.exponential(1)*rng.choice([0.2,1,3])
        vals,psi=run(N,L,cw,Jn); d=np.diff(psi); r=d.max()/np.abs(psi).max()
        if r>worst: worst=r; print(N,L,round(cw,3),round(Jn,3),'max rel increase',r, np.round(psi,4),flush=True)
print('worst',worst)
