import numpy as np, itertools
rng=np.random.default_rng(2)
def conn(J):
    n=len(J);seen={0};st=[0]
    while st:
        i=st.pop()
        for j in range(n):
            if J[i,j]>0 and j not in seen: seen.add(j);st.append(j)
    return len(seen)==n
def test(n,J,r,a,b):
    S=np.array(list(itertools.product([-1,1],repeat=n)),float)
    E=np.einsum('ki,ij,kj->k',S*r,J,S*r)/2
    w=np.exp(E-E.max())*S[:,a]*S[:,b]
    if w.sum()/np.abs(w).sum()<1e-6: return np.inf,None
    L=(S*r)*((S*r)@J)
    Zab=w.sum(); m=(w[:,None]*L).sum(0)/Zab
    C=(w[:,None,None]*L[:,:,None]*L[:,None,:]).sum(0)/Zab-np.outer(m,m)
    K=(w[:,None,None]*(S*r)[:,:,None]*(S*r)[:,None,:]).sum(0)/Zab*J
    C=C+K+np.diag(m)
    # normalize: cov of degrees relative to sqrt var
    d=np.sqrt(np.abs(np.diag(C)));Cn=C/np.outer(d,d)
    np.fill_diagonal(Cn,np.inf); Cn=Cn[:,-1:]
    i,j=np.unravel_index(np.argmin(Cn),Cn.shape)
    return Cn.min(),(i,j)
worst=np.inf
for trial in range(30000):
    n=rng.integers(2,7)
    J=rng.exponential(1,(n,n))*(rng.random((n,n))<0.6); J=np.triu(J,1); J=J+J.T
    if not conn(J): continue
    r=rng.exponential(1,n)*rng.choice([0.1,0.5,1,2],n)
    a,b=rng.choice(n,2,replace=False)
    v,ij=test(n,J,r,a,b)
    if v<worst: worst=v; print(trial,n,v,ij,(a,b),flush=True); last=(J,r,a,b)
np.save('worstL.npy',np.array([last],dtype=object),allow_pickle=True)
