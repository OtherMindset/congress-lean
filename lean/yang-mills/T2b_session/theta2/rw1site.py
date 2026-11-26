# One-site check of the BFS/Symanzik random-walk (RW) bounds with a field.
# g(s)=exp(-2a s-4b s^2), s=phi^2/2 (site weight e^{-a phi^2-b phi^4}).
# Z(t)=int e^{h phi} g(phi^2/2+t) dphi.  m=h int Z(t)dt/Z, T=h int t Z(t)dt/Z,
# B=h^2 int int Z(t1+t2)/Z = h T  (one site).  Checks:
#  (i) m - h chi = h(m^2 - B)  (exact RW identity)
#  (ii) m - h chi <= 8 b h T^2  (from Z(t1+t2)Z >= e^{-8b t1 t2} Z(t1)Z(t2))
#  (iii) S=<phi;phi^2> = 2T - 2Delta with Delta>=0
import numpy as np
from scipy import integrate
def moments(a,b,h):
    ph=np.linspace(-7,7,2801); s=ph**2/2
    w=lambda t: np.exp(h*ph-2*a*(s+t)-4*b*(s+t)**2)
    Zf=lambda t: np.trapezoid(w(t),ph)
    tmax=40.0
    ts=np.linspace(0,tmax,4001)
    Zt=np.array([Zf(t) for t in ts]); Z=Zt[0]
    I0=np.trapezoid(Zt,ts)/Z; I1=np.trapezoid(ts*Zt,ts)/Z
    p=np.exp(h*ph-a*ph**2-b*ph**4); p/=np.trapezoid(p,ph)
    E=lambda f: np.trapezoid(f*p,ph)
    m=E(ph); m2=E(ph**2); m3=E(ph**3)
    chi=m2-m*m; S=m3-m*m2
    return m,chi,S,h*I0,h*I1
print(" a     b     h   |  m      m(RW)  | m-h chi   h(m^2-hT) | 8bhT^2/(m-hchi) | T/(S/2) ")
for a,b in [(2.0,0.02),(2.0,0.2),(1.0,1.0),(0.0,1.0),(-1.0,1.0),(-2.0,1.0),(-4.0,1.0)]:
    for h in [0.05,0.3,1.0]:
        m,chi,S,mrw,T=moments(a,b,h)
        lhs=m-h*chi
        print(f"{a:5.1f} {b:5.2f} {h:4.2f} | {m:.5f} {mrw:.5f} | {lhs:.3e} {h*(m*m-h*T):.3e} | {8*b*h*T*T/lhs:10.3f} | {T/(S/2):8.3f}")
