# Prop 7.2 on two sites (single bond J): exact walk local-time density, quadrature.
import numpy as np
from scipy.special import iv
def run(a,b,J,H,nphi=160,Lp=5.0,nt=48,Tm=7.0):
    x,wx=np.polynomial.legendre.leggauss(nphi); x=x*Lp; wx=wx*Lp
    X0,X1=np.meshgrid(x,x,indexing='ij'); W=np.outer(wx,wx)
    base=J*X0*X1+H*(X0+X1)
    def model(a0,a1,Hh=H):  # returns Z, m0, m1, and moments
        E=J*X0*X1+Hh*(X0+X1)-a0*X0**2-a1*X1**2-b*(X0**4+X1**4)
        P=W*np.exp(E); Z=P.sum()
        return Z,(P*X0).sum()/Z,(P*X1).sum()/Z,P/Z
    Z,m,_,P=model(a,a)
    S=((P*X0*(X0**2+X1**2)).sum()-m*(P*(X0**2+X1**2)).sum())  # -d_a m
    chi=(P*X0*(X0+X1)).sum()-m*(P*(X0+X1)).sum()
    g=lambda t: np.exp(-2*a*t-4*b*t**2)
    t,wt=np.polynomial.legendre.leggauss(nt); t=(t+1)*Tm/2; wt=wt*Tm/2
    # Z(t0,t1)/Z = g(t0)g(t1) Z_{a+4bt0,a+4bt1}/Z ; m^{(t)}
    Zr=np.zeros((nt,nt)); m0r=np.zeros((nt,nt)); m1r=np.zeros((nt,nt))
    for i in range(nt):
        for j in range(nt):
            z,u,v,_=model(a+4*b*t[i],a+4*b*t[j]); Zr[i,j]=g(t[i])*g(t[j])*z/Z; m0r[i,j]=u; m1r[i,j]=v
    Zl=np.zeros(nt); m0l=np.zeros(nt); m1l=np.zeros(nt)  # t1=0 line
    for i in range(nt):
        z,u,v,_=model(a+4*b*t[i],a); Zl[i]=g(t[i])*z/Z; m0l[i]=u; m1l[i]=v
    T0,T1=np.meshgrid(t,t,indexing='ij'); WT=np.outer(wt,wt)
    s=2*J*np.sqrt(T0*T1)
    rho=H*J*(iv(0,s)+np.sqrt(T0/T1)*iv(1,s))
    I2=lambda f:(WT*rho*Zr*f).sum()
    I1=lambda f:(wt*H*Zl*f).sum()
    mass=I2(1)+I1(1)
    T=I2(T0+T1)+I1(t)
    id1=I2(m0r)+I1(m0l)
    lhs=m-H*chi
    W3=H*(I2(2*m-m0r-m1r)+I1(2*m-m0l-m1l))
    tang=I2(4*b*(T0+T1)*S)+I1(4*b*t*S)
    Keff=(W3/H)/tang
    return dict(m=m,mass=mass,HT=H*T,id1=id1,m2=m*m,lhs=lhs,W3=W3,bound2=8*b*H*T*T,
                Keff=Keff,check3=4*Keff*b*H*T*S)
for p in [(1,0.5,0.5,0.3),(-1,1,0.5,0.5),(0.5,0.3,1.0,0.2)]:
    for nt in (32,48):
        r=run(*p,nt=nt); print(p,nt,' '.join('%s=%.7g'%(k,v) for k,v in r.items()))
