# Curie-Weiss phi^4, exact HS quadrature. Tests Form I of STATEMENT.md:
#   r_theta(h) = (m - h chi) / (4 b m^theta (-d_a m)),  K_theta(s0) = sup_{m<=s0} r_theta.
# L (K=0) <=> K_2 <= 1 everywhere.  (CW identity: m - h chi = 4b m^2 dR/dh + 4b m^2 (-d_a m).)
import numpy as np, sys
from scipy.interpolate import CubicSpline
def site(a,b,W):
    phi=np.linspace(-12,12,6001); w=np.linspace(-W,W,8001)
    E=-(a*phi**2+b*phi**4)[None,:]+w[:,None]*phi[None,:]
    mx=E.max(1,keepdims=True); P=np.exp(E-mx); z=P.sum(1)
    g=CubicSpline(w,np.log(z)+mx[:,0]); p2=CubicSpline(w,(P*phi**2).sum(1)/z)
    p1=CubicSpline(w,(P*phi).sum(1)/z); p3=CubicSpline(w,(P*phi**3).sum(1)/z)
    return g,p1,p2,p3
def obs(S,J,N,h,W):
    g,p1,p2,p3=S
    w=np.linspace(-W,W,400001)
    lw=-N*(w-h)**2/(2*J)+N*g(w); lw-=lw.max(); P=np.exp(lw); P/=P.sum()
    Ew=(P*w).sum(); dw=w-Ew; Vw=(P*dw*dw).sum()
    m=(Ew-h)/J; chi=N*Vw/J**2-1/J
    q2=p2(w); dam=(N/J)*(P*dw*(q2-(P*q2).sum())).sum()   # = -d_a m
    # R for identity check
    M1=(P*p1(w)).sum(); M2=(P*q2).sum(); M3=(P*p3(w)).sum()
    return m,chi,dam,(M3-M1*M2)/M1,M1
if __name__=="__main__":
    a,b,J=[float(x) for x in sys.argv[1:4]]
    W=J*6+4; S=site(a,b,W+2)
    hs=np.exp(np.linspace(np.log(1e-7),np.log(1.0),90))
    for N in [16,64,256,1024,4096]:
        res=np.array([obs(S,J,N,h,W) for h in hs])
        m,chi,dam=res[:,0],res[:,1],res[:,2]
        # identity check at a few points via finite-difference dR/dh
        Rv=res[:,3]; dR=np.gradient(Rv,hs)
        lhs=m-hs*chi; rhs=4*b*m**2*dR+4*b*m**2*dam
        ok=np.abs(lhs-rhs)/np.maximum(np.abs(lhs),1e-300)
        out=[]
        Mplus=m[-1]
        for th in [2.0,1.5,1.0,0.5]:
            r=lhs/(4*b*m**th*dam)
            row=[]
            for s0 in [0.05,0.1,0.2,0.4,0.8]:
                sel=(m<=s0)&(m>1e-3*s0)
                row.append(r[sel].max() if sel.any() else np.nan)
            out.append(row)
        print(f"a={a} b={b} J={J} N={N} m(h=1)={m[-1]:.3f} m/h@1e-7={m[0]/hs[0]:.3g} idcheck(med rel)={np.median(ok[5:-5]):.1e} minLHS={lhs.min():.2e}")
        for th,row in zip([2.0,1.5,1.0,0.5],out):
            print(f"   theta={th}: sup r over m<=s0 for s0=0.05,0.1,0.2,0.4,0.8:", " ".join(f"{v:9.4f}" for v in row))
