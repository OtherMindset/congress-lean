import numpy as np, itertools
exec(open('isingL3g.py').read().split('worst=np.inf')[0])
rng=np.random.default_rng(3)
worst=np.inf
for trial in range(20000):
    n=rng.integers(2,7)  # real sites
    kind=rng.integers(3)
    J=np.zeros((n+1,n+1))
    Jv=rng.exponential(1)*rng.choice([0.1,1,3])
    for i in range(n):
        if kind==0 and i+1<n: J[i,i+1]=Jv   # path
        if kind==1: J[i,(i+1)%n]=Jv          # ring
        if kind==2:
            for j in range(i+1,n): J[i,j]=Jv*(rng.random()<0.7)
    J=np.maximum(J,J.T)
    J[:n,n]=J[n,:n]=1.0
    r=rng.exponential(1,n+1)*rng.choice([0.2,1,2],n+1)
    v,ij=test(n+1,J,r,0,n)
    if v<worst: worst=v; print(trial,kind,n,v,ij,np.round(r,3),Jv,flush=True)
