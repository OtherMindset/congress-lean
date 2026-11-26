# Curie-Weiss phi^4 (exact HS quadrature): uniform-mass "no-plateau" constant
#   K_unif(a,h) = sup_{d>0} [m(a) - m(a+d)] / (d * (-d_a m)(a))
# and the screening number 2b*chi2, chi2 = Var(sum phi^2)/N = -d_a <phi^2>.
import numpy as np, sys
from scipy.interpolate import CubicSpline
def site(a,b,W):
    phi=np.linspace(-14,14,2801); w=np.linspace(-W,W,3001)
    E=-(a*phi**2+b*phi**4)[None,:]+w[:,None]*phi[None,:]
    mx=E.max(1,keepdims=True); P=np.exp(E-mx); z=P.sum(1)
    f=lambda k: CubicSpline(w,(P*phi**k).sum(1)/z)
    return CubicSpline(w,np.log(z)+mx[:,0]),f(1),f(2),f(4)
def obs(S,J,N,h,W):
    g,p1,p2,p4=S
    w=np.linspace(-W,W,200001)
    lw=-N*(w-h)**2/(2*J)+N*g(w); lw-=lw.max(); P=np.exp(lw); P/=P.sum()
    Ew=(P*w).sum(); dw=w-Ew
    m=(Ew-h)/J
    q2=p2(w); dam=(N/J)*(P*dw*(q2-(P*q2).sum())).sum()
    E2=(P*q2).sum(); v2=(P*(p4(w)-q2**2)).sum(); chi2=v2+N*((P*q2*q2).sum()-E2**2)
    return m,dam,chi2
a,b,J=[float(x) for x in sys.argv[1:4]]
W=J*5+4
ds=np.concatenate([np.linspace(0.002,0.05,12),np.linspace(0.06,1.0,20)])*max(abs(J-2*a),0.2)
S0=site(a,b,W+2); Sd=[site(a+d,b,W+2) for d in ds]
for N in [64,256,1024]:
    # flip scale: h such that h*N*M ~ x
    mbig=obs(S0,J,N,0.05,W)[0]
    for x in [0.1,0.3,1.0,3.0]:
        h=x/(N*max(mbig,1e-3))
        m,dam,chi2=obs(S0,J,N,h,W)
        md=np.array([obs(Sd[i],J,N,h,W)[0] for i in range(len(ds))])
        r=(m-md)/(ds*dam)
        print(f"N={N} x={x} h={h:.2e} m={m:.4f} S=-d_a m={dam:.4g} 2b chi2={2*b*chi2:.3f} K_unif={r.max():.3f} at d={ds[r.argmax()]:.3g}")
