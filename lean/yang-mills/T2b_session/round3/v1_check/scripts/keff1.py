# one-site walk K_eff (exact walk-shaped secant/tangent), numpy quadrature
import numpy as np
def keff(a,b,H,L=None,ng=4000,nt=400):
    if L is None: L=np.sqrt(max(-a,0)/(2*b))*1.0+6/ (b**0.25)
    x,w=np.polynomial.legendre.leggauss(ng); x*=L; w*=L
    def mom(aa):
        E=-aa*x**2-b*x**4+H*x; P=w*np.exp(E-E.max()); return P/P.sum()
    P=mom(a); m=(P*x).sum(); S=(P*x**3).sum()-m*(P*x**2).sum(); chi=(P*x*x).sum()-m*m
    # Z(t)/Z = g(t) Z_{a+4bt}/Z_a with g(t)=exp(-2at-4bt^2)
    E0=-a*x**2-b*x**4+H*x; c=E0.max(); Z=(w*np.exp(E0-c)).sum()
    tmax=(abs(a)+10)/(2*b) if a<0 else 10/np.sqrt(b)+5
    t,wt=np.polynomial.legendre.leggauss(nt); t=(t+1)*tmax/2; wt*=tmax/2
    num=0;den=0;mass=0
    for ti,wi in zip(t,wt):
        aa=a+4*b*ti; E=-aa*x**2-b*x**4+H*x
        Zr=np.exp(-2*a*ti-4*b*ti**2)*(w*np.exp(E-c)).sum()/Z
        mr=(w*x*np.exp(E-c)).sum()/(w*np.exp(E-c)).sum()
        mass+=wi*H*Zr; num+=wi*H*Zr*(m-mr); den+=wi*H*Zr*4*b*ti*S
    return dict(m=m,mass=mass,Keff=num/den,check=(H*num)/(m-H*chi))
for p in [(2,0.02,0.5),(-2.71,0.0226,0.409),(-4,1,0.2),(-2,1,1),(-8,1,0.05)]:
    print(p,keff(*p))
