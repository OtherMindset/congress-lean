import numpy as np
from numpy import trapezoid as tz
phi=np.linspace(-9,9,20001)
def onesite(V,H):
    w=np.exp(-V(phi)+H*phi-(-V(phi)+H*phi).max())
    Z=tz(w,phi); mo=[tz(w*phi**k,phi)/Z for k in range(4)]
    return mo
# (1) one-site R monotone (EMN class) + a non-EMN double well
Vs={'x2+x4':lambda x:x**2+x**4,'-3x2+x4':lambda x:-3*x**2+x**4,'-10x2+x4':lambda x:-10*x**2+x**4,'cosh2x-3x2':lambda x:np.cosh(2*x)-3*x**2,'-x2+x8':lambda x:-x**2+x**8}
Hs=np.linspace(0.01,5,120)
for k,V in Vs.items():
    R=[]
    for H in Hs:
        _,m1,m2,m3=onesite(V,H); R.append((m3-m1*m2)/m1)
    d=np.diff(R); print(f"R mono {k}: max dR={d.max():.2e} (should be <=0)")
# (2) RW1 on one site: m-Hchi <= 8bH T^2, T=H int t Zhat(t) dt ; also m=H int Zhat
def rw1(a,b,H):
    s=phi**2/2; g=lambda u:np.exp(-2*a*u-4*b*u**2)
    base=-a*phi**2-b*phi**4+H*phi; c=base.max(); wb=np.exp(base-c); Z=tz(wb,phi)
    ts=np.linspace(0,20,2001)
    Zh=np.array([tz(np.exp(H*phi-c)*g(s+t),phi)/Z for t in ts])
    m=H*tz(Zh,ts); T=H*tz(ts*Zh,ts)
    mo=[tz(wb*phi**k,phi)/Z for k in range(3)]
    h2=1e-4; mp=tz(np.exp(-a*phi**2-b*phi**4+(H+h2)*phi-c)*phi,phi)/tz(np.exp(-a*phi**2-b*phi**4+(H+h2)*phi-c),phi)
    mm=tz(np.exp(-a*phi**2-b*phi**4+(H-h2)*phi-c)*phi,phi)/tz(np.exp(-a*phi**2-b*phi**4+(H-h2)*phi-c),phi)
    chi=(mp-mm)/(2*h2)
    return m,mo[1],(m-H*chi),8*b*H*T**2
for (a,b,H) in [(2,0.02,0.5),(2,0.2,0.5),(1,1,0.3),(-2,1,0.3),(-4,1,1.0),(0.5,1,3.0)]:
    m,mdir,lhs,rhs=rw1(a,b,H)
    print(f"RW1 a={a} b={b} H={H}: m_walk={m:.6f} m_direct={mdir:.6f}  m-Hchi={lhs:.4e} 8bHT^2={rhs:.4e} ratio={rhs/lhs:.3f}")
