import numpy as np
def ks(a,H):
    t=np.tanh(a*H); S=1-t**2
    return a*t, a**2*S, -2*a**3*S*t, 2*a**4*S*(2*t**2-S)
rng=np.random.default_rng(1); worst=-np.inf
for trial in range(60000):
    n=rng.integers(1,7); A=rng.exponential(1,n)*rng.choice([0.1,1,10],n); beta=rng.choice([0,rng.exponential(1)*rng.choice([0.01,1,100])])
    Hs=np.geomspace(1e-2,10,30)/A.max()
    k=[0,0,0,0]
    for ai in A:
        kk=ks(ai,Hs); k=[k[i]+kk[i] for i in range(4)]
    k[0]=k[0]+2*beta*Hs; k[1]=k[1]+2*beta
    T=2*k[0]**2*k[2]+k[0]*k[3]-k[1]*k[2]
    r=(T/(k[0]*k[1]**2+k[0]**3*k[1])).max()
    if r>worst: worst=r; print(trial,n,np.round(A,3),beta,r,flush=True)
