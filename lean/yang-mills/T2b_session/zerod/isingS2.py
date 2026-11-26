import numpy as np, itertools,sys
rng=np.random.default_rng(int(sys.argv[1]))
mode=sys.argv[2]  # 'rand' or 'gs'
def deriv(Sp,E0,MB,M,H):
    lw=E0+H*M; w=np.exp(lw-lw.max()); w/=w.sum()
    Ex=lambda f:(w*f).sum()
    a=MB-Ex(MB); a2=MB**2-Ex(MB**2); Mc=M-Ex(M)
    m=Ex(MB); c=Ex(a*a2)
    dc=Ex(a*a2*Mc)  # joint cumulant k(a,a2,M) (centered triple moment)
    dm=Ex(a*Mc)
    return (dc*m-c*dm)/m**2, c/m, dm
worst=-np.inf; Hs=[0.02,0.1,0.3,0.7,1.5,3]
for trial in range(3000):
    if mode=='rand':
        n=rng.integers(3,11); J=rng.exponential(1,(n,n))*(rng.random((n,n))<rng.random()); J=np.triu(J,1)*rng.choice([0.1,0.3,1]); J=J+J.T
        k=rng.integers(2,n+1); B=list(rng.choice(n,k,replace=False))
    else: # GS: blocks of size N on L sites (path/ring), CW coupling inside block c/N, inter-block J*alpha^2
        N=rng.integers(2,5); L=rng.integers(1,4) if N<4 else rng.integers(1,3); n=N*L
        cw=rng.uniform(0.2,2.0); Jn=rng.exponential(0.5)
        J=np.zeros((n,n))
        for b in range(L):
            for i in range(N):
                for j in range(N):
                    if i!=j: J[b*N+i,b*N+j]=cw/N
            nb=[(b+1)%L] if L>2 else ([b+1] if b+1<L else [])
            for c in nb:
                for i in range(N):
                    for j in range(N): J[b*N+i,c*N+j]+=Jn/N; J[c*N+j,b*N+i]+=Jn/N
        B=list(range(N))
    Sp=np.array(list(itertools.product([-1,1],repeat=n)),float)
    E0=np.einsum('ki,ij,kj->k',Sp,J,Sp)/2; MB=Sp[:,B].sum(1); M=Sp.sum(1)
    for H in Hs:
        d,S,dm=deriv(Sp,E0,MB,M,H)
        if S<1e-6: continue
        rel=d/(abs(S)*dm/ (np.abs(MB).max()) +1e-30)
        if d/S>worst: worst=d/S; print(trial,n,len(B),H,'dS/S',d/S,'S',S,flush=True); np.save(f'worst_{mode}.npy',np.array([J,B,H],dtype=object),allow_pickle=True)
