# Lambda(p) = Cov_p(y^2, U'(y)/y), U=-log p, for 1D even densities; compare with |B|/3.
import numpy as np
def stats(p,y):
    dy=y[1]-y[0]; p=p/(p.sum()*dy)
    U=-np.log(p); dU=np.gradient(U,dy); g=np.where(np.abs(y)>1e-9,dU/np.where(y==0,1,y),np.nan)
    ok=~np.isnan(g)
    E=lambda f:(p[ok]*f[ok]).sum()*dy
    m2=E(y**2); m4=E(y**4)
    return E(y**2*g)-m2*E(g), 3-m4/m2**2
y=np.linspace(-8,8,160001)   # grid avoids y=0? includes 0 -> masked
G=lambda c,s: np.exp(-(y-c)**2/(2*s*s))
print("gaussian  Lambda=%.4f |B|=%.4f"%stats(G(0,1),y))
print("bimodal   Lambda=%.4f |B|=%.4f"%stats(G(2,.3)+G(-2,.3),y))
for s in (0.6,0.4,0.3):
    print("trimodal (sum of two indep. bimodals), width %.1f: Lambda=%.4f |B|=%.4f"%((s,)+stats(G(2,s)+G(-2,s)+2*G(0,s),y)))
