import numpy as np, sys
def mchain(a,b,J,H,ng,L):
    g=np.linspace(-L,L,ng)
    V=np.exp(H*g-a*g**2-b*g**4)
    K=np.exp(J*np.outer(g,g))
    sv=np.sqrt(V)
    T=sv[:,None]*K*sv[None,:]
    w,U=np.linalg.eigh(T); psi=U[:,-1]
    return (psi**2*g).sum()
def extent(a,b,J,H):
    c=max(2*J-a,0)
    for L in np.arange(0.5,30,0.25):
        if b*L**4-c*L**2-H*L>40: return L
    return 30
def kapU(a,b,J,H,ng=200,d=0.04):
    L=extent(a,b,J,H)
    f=lambda x: mchain(x,b,J,H,ng,L)
    m=[f(a+k*d) for k in (-2,-1,0,1,2)]
    d2=(-m[0]+16*m[1]-30*m[2]+16*m[3]-m[4])/(12*d*d)
    d1=(m[0]-8*m[1]+8*m[3]-m[4])/(12*d)
    return d2,d1,m[2]
if __name__=="__main__":
    rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
    rows=[]
    for i in range(N):
        a=rng.uniform(-4,4); b=np.exp(rng.uniform(np.log(.02),np.log(2))); J=np.exp(rng.uniform(np.log(.1),np.log(3))); H=np.exp(rng.uniform(np.log(.01),np.log(3)))
        d2,d1,m=kapU(a,b,J,H)
        rows.append((a,b,J,H,d2,d1,m))
    r=np.array(rows); np.save('chain_%s.npy'%sys.argv[1],r)
    neg=r[:,4]<0
    print('chain n',len(r),'frac U<0',neg.mean(),'worst d2/|d1|',(r[:,4]/abs(r[:,5])).min())
    print('neg a max',r[neg][:,0].max() if neg.any() else None)
    i=np.argmin(r[:,4]/abs(r[:,5])); print(r[i])
