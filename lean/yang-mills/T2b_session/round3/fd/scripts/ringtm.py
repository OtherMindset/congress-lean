# Exact (quadrature + transfer matrix) zero-field quantities for the phi^4 ring.
# weight exp(J sum phi_i phi_{i+1} - sum(a phi^2 + b phi^4)), N sites, periodic.
import numpy as np
from numpy.polynomial.legendre import leggauss
def grid(a,b,J,ng=200):
    R=1.0
    while (a-J)*R*R+b*R**4 < 50: R+=0.05
    x,w=leggauss(ng); return R*x,R*w
class Ring:
    def __init__(s,a,b,J,N,ng=200):
        s.a,s.b,s.J,s.N=a,b,J,N
        x,w=grid(a,b,J,ng); s.x=x
        V=a*x*x+b*x**4
        sw=np.sqrt(w)
        T=np.exp(J*np.outer(x,x)-0.5*V[:,None]-0.5*V[None,:])*np.outer(sw,sw)
        ev,U=np.linalg.eigh(T)
        lm=ev.max(); s.ev=ev/lm; s.U=U
        s.lam=s.ev**N; s.Z=s.lam.sum()
        s.D=U.T@(x[:,None]*U)   # phi in eigenbasis
    def G(s):
        # G(0,z) = sum_{ij} D_ij^2 ev_i^{N-z} ev_j^z / Z
        N=s.N; D2=s.D**2; e=s.ev
        out=np.empty(N)
        for z in range(N):
            out[z]=(e**(N-z))@D2@(e**z)/s.Z
        return out
    def moments_M(s,K=48):
        # E M^2, E M^4 via Cauchy integral of Z(H)/Z(0) on a circle
        N=s.N; G=s.G(); X=N*G.sum()
        r=1.0/np.sqrt(X)   # scale: H*sqrt(<M^2>) ~ 1
        th=2*np.pi*np.arange(K)/K
        vals=[]
        sw=None
        for t in th:
            H=r*np.exp(1j*t)
            vals.append(s.ZH(H))
        vals=np.array(vals)
        c=np.fft.fft(vals)/K   # c_n r^n
        M2=2*(c[2]/r**2).real; M4=24*(c[4]/r**4).real
        return M2,M4,G
    def ZH(s,H):
        # Z(H)/Z(0) ; T(H)=E T E with E=diag(exp(H x/2)) in original basis
        x=s.x; U=s.U
        E=np.exp(0.5*H*x)
        TH=(U*s.ev)@U.T   # normalized T in grid basis
        TH=(E[:,None]*TH)*E[None,:]
        ev=np.linalg.eigvals(TH)
        return (ev**s.N).sum()/s.Z
def quantities(a,b,J,N,ng=200):
    R=Ring(a,b,J,N,ng); M2,M4,G=R.moments_M()
    m2=M2/N**2; B=M4/M2**2-3
    chi=G.sum(); B2=(G**2).sum()
    return dict(m2=m2,B=B,chi=chi,B2=B2,G=G,phi2=G[0])
def m2_only(a,b,J,N,ng=200):
    R=Ring(a,b,J,N,ng); return R.G().sum()/N
if __name__=="__main__":
    q=quantities(0.5,1.0,0.0,1)
    from mpmath import quad,exp,inf
    z=[quad(lambda t:t**k*exp(-0.5*t*t-t**4),[-inf,0,inf]) for k in (0,2,4)]
    print(q['m2'],z[1]/z[0], q['B']+3, (z[2]/z[0])/(z[1]/z[0])**2)

