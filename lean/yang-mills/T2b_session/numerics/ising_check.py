# brute-force check of ising_strip on a W x L periodic-length strip
import numpy as np, itertools, ising_strip as I
def brute(W, Lr, beta, H, B, c0):
    N = W*Lr; best = {}
    S = np.array(list(itertools.product([-1,1], repeat=N)), float).reshape(-1, Lr, W)
    E = beta*np.sum(S*np.roll(S,-1,axis=1),axis=(1,2))
    if W>=3: E += beta*np.sum(S*np.roll(S,-1,axis=2),axis=(1,2))
    elif W==2: E += beta*np.sum(S[:,:,0]*S[:,:,1],axis=1)
    c = np.full((Lr,W), c0); c[0][B] = 1.0
    # B pattern repeats per column (k=1)
    for col in range(Lr): c[col][B] = 1.0
    Phi = np.einsum('slw,lw->s', S, c); MB = S[:,0,:][:,B].sum(1)
    w = np.exp(E + H*Phi - (E+H*Phi).max()); w/=w.sum()
    Ex=lambda f:(w*f).sum(); Sx=lambda f:Ex(f*Phi)-Ex(f)*Ex(Phi)
    m=Ex(MB); P=Ex(MB**2); u=Ex(MB**3)-m*P; up=Sx(MB**3)-m*Sx(MB**2)-P*Sx(MB); chi=Sx(MB)
    return (up*m-u*chi)/m**2, u/m
for W,Bm,c0 in [(3,[True,True,False],0.3),(3,[True,True,True],1.0),(2,[True,False],0.5)]:
    Bmask=np.array(Bm)
    T,MB,Phi=I.supercol(W,1,0.45,0.45,0.2,Bmask,c0)
    q=I.ic_quantities(T,MB,Phi,4); print(W, q['Rp'], q['R'], brute(W,4,0.45,0.2,Bmask,c0))
# k=2 check against brute force: W=3, 2 supercolumns (L=4 columns), B = first two columns
def brute2(W, Lc, beta, H, Bcols, c0):
    N=W*Lc; S=np.array(list(itertools.product([-1,1],repeat=N)),float).reshape(-1,Lc,W)
    E=beta*np.sum(S*np.roll(S,-1,axis=1),axis=(1,2))+beta*np.sum(S*np.roll(S,-1,axis=2),axis=(1,2))
    c=np.full((Lc,W),c0)
    for col in range(Lc):
        if col%2 in Bcols: c[col]=1.0
    Phi=np.einsum('slw,lw->s',S,c); MB=S[:,list(Bcols),:].sum((1,2))
    w=np.exp(E+H*Phi-(E+H*Phi).max()); w/=w.sum()
    Ex=lambda f:(w*f).sum(); Sx=lambda f:Ex(f*Phi)-Ex(f)*Ex(Phi)
    m=Ex(MB);P=Ex(MB**2);u=Ex(MB**3)-m*P;up=Sx(MB**3)-m*Sx(MB**2)-P*Sx(MB);chi=Sx(MB)
    return (up*m-u*chi)/m**2, m
T,MB,Phi=I.supercol(3,2,0.4,0.4,0.05,np.ones(6,bool),0.3); q=I.ic_quantities(T,MB,Phi,2); print('k2 all',q['Rp'],q['m'],brute2(3,4,0.4,0.05,(0,1),0.3))
Bm=np.array([1,1,1,0,0,0],bool)
T,MB,Phi=I.supercol(3,2,0.4,0.4,0.05,Bm,0.3); q=I.ic_quantities(T,MB,Phi,2); print('k2 col',q['Rp'],q['m'],brute2(3,4,0.4,0.05,(0,),0.3))
