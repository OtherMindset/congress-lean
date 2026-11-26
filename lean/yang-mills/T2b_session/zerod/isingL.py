# Test lemma (L): r -> log sum_s s_a s_b exp(sum J_xy r_x r_y s_x s_y) supermodular, i.e.
# Cov_{P^{ab}}(d_x,d_y) >= 0 computed via signed spin measure.
import numpy as np, itertools
rng=np.random.default_rng(1)
def test(n,J,r,a,b):
    S=np.array(list(itertools.product([-1,1],repeat=n)),float)
    E=np.einsum('ki,ij,kj->k',S*r,J,S*r)/2
    w=np.exp(E-E.max())*S[:,a]*S[:,b]
    L=(S*r)*((S*r)@J)   # L_x = sum_z J r_x r_z s_x s_z
    Zab=w.sum()
    m=(w[:,None]*L).sum(0)/Zab
    C=(w[:,None,None]*L[:,:,None]*L[:,None,:]).sum(0)/Zab-np.outer(m,m)
    np.fill_diagonal(C,np.inf)
    return C.min()
worst=np.inf
for trial in range(20000):
    n=rng.integers(2,7)
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<0.6); J=np.triu(J,1); J=J+J.T
    r=rng.exponential(1,n)*rng.choice([0.1,1,3],n)
    a,b=rng.choice(n,2,replace=False)
    v=test(n,J,r,a,b)
    if v<worst: worst=v; print(trial,n,v,flush=True)
