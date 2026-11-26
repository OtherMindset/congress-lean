# (UNI_kappa) test on rings: X(a+s) vs X(a+kappa*mean(s)) for non-uniform s>=0.  X=<M^2>.
import numpy as np
from numpy.polynomial.legendre import leggauss
def X(avec,b,J,ng=160):
    N=len(avec); amin=min(avec)
    R=1.0
    while (amin-J)*R*R+b*R**4<40: R+=0.05
    x,w=leggauss(ng); x=R*x; w=R*w
    def lz(H):
        P=None
        for i in range(N):
            a1=avec[i]; a2=avec[(i+1)%N]
            T=np.exp(J*np.outer(x,x)-0.5*(a1*x*x+b*x**4-H*x)[:,None]-0.5*(a2*x*x+b*x**4-H*x)[None,:])*w[None,:]
            P=T if P is None else P@T
            sc=np.abs(P).max(); P=P/sc
            lz.s+=np.log(sc)
        return np.log(np.trace(P))
    def L(H):
        lz.s=0.0; t=lz(H); return t+lz.s
    l0=L(0.0); h=1e-3
    for it in range(8):
        M2=2*(np.exp(L(h)-l0)-1)/h**2; hn=0.2/np.sqrt(M2)
        if abs(hn-h)<0.1*h: break
        h=hn
    hs=h*np.array([1,2,3.]); r=np.array([np.exp(L(q)-l0)-1 for q in hs])
    A=np.array([[q**2,q**4,q**6] for q in hs]); c=np.linalg.solve(A,r)
    return 2*c[0]
from scipy.optimize import brentq
print("# ring, b, J, a | pattern | X0, X(a+s), X(a+mean s) | kappa needed")
for (N,a,b,J) in [(8,0.6,0.02,1.0),(8,0.9,0.02,1.0),(8,0.5,0.5,1.0),(8,-1.0,0.5,1.0),(8,1.1,0.1,1.0)]:
    X0=X([a]*N,b,J)
    f=X0/N**2
    for name,pat in [("half-half",[1]*(N//2)+[0]*(N//2)),("alternating",[1,0]*(N//2)),("one site",[1]+[0]*(N-1))]:
        for amp in [0.5,2.0,8.0]:
            s=np.array(pat,float); s=s/s.mean()*(amp*4*b*f)   # mean(s)=amp*4 b f(a)
            Xs=X(list(a+s),b,J); Xu=X([a+s.mean()]*N,b,J)
            g=lambda k: X([a+k*s.mean()]*N,b,J)-Xs
            try: kk=brentq(g,1e-6,50,xtol=1e-4)
            except Exception: kk=float('nan')
            print(N,a,b,J,"| %-11s amp=%.1f | %.4g %.4g %.4g | kappa=%.3f"%(name,amp,X0,Xs,Xu,kk))
