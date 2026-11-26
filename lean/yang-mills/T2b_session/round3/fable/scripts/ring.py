# 1D ring (N sites, coupling J per bond): weight exp(J sum phi_i phi_{i+1} - sum(a phi^2+b phi^4) + H sum phi)
# zero-field moments of M via even-polynomial extrapolation of Z(H)/Z(0).
import numpy as np
from numpy.polynomial.legendre import leggauss
def setup(a,b,J,ng=240):
    # box: potential a phi^2 + b phi^4 - J phi^2 (ring coordination 2)
    R=1.0
    while (a-J)*R*R+b*R**4 < 45: R+=0.05
    x,w=leggauss(ng); return R*x,R*w
def Zring(a,b,J,N,H,x,w):
    V=a*x*x+b*x**4-H*x
    T=np.exp(J*np.outer(x,x)-0.5*V[:,None]-0.5*V[None,:])*np.sqrt(w[:,None]*w[None,:])
    ev=np.linalg.eigvalsh(T)
    ev=ev[ev>0]
    lm=ev.max()
    return N*np.log(lm)+np.log(((ev/lm)**N).sum())
def mom(a,b,J,N,ng=240):
    x,w=setup(a,b,J,ng)
    l0=Zring(a,b,J,N,0.0,x,w)
    # rough m2 by small H
    h=1e-3
    for it in range(6):
        r=np.exp(Zring(a,b,J,N,h,x,w)-l0)-1
        M2=2*r/h**2
        hn=0.25/np.sqrt(M2)
        if abs(hn-h)<0.2*h: break
        h=hn
    hs=h*np.array([1,2,3,4,5.])
    r=np.array([np.exp(Zring(a,b,J,N,hh,x,w)-l0)-1 for hh in hs])
    # r = c1 H^2 + c2 H^4 + ... + c5 H^10
    A=np.array([[hh**(2*k) for k in range(1,6)] for hh in hs])
    c=np.linalg.solve(A,r)
    M2=2*c[0]; M4=24*c[1]
    return M2/N**2, M4/N**4
if __name__=="__main__":
    # check vs 1-site (N=1, J=0)
    print(mom(0.5,1,0.0,1))
    from mpmath import quad,exp,inf
    z=[quad(lambda t:t**k*exp(-0.5*t*t-t**4),[-inf,0,inf]) for k in (0,2,4)]
    print(z[1]/z[0],z[2]/z[0])
