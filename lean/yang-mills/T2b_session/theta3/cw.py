# Curie-Weiss phi^4: weight exp((J/2N)M^2 - sum(a phi^2 + b phi^4) + H M)
# Exact finite-N conditional-on-M quantities by saddle-point contour inversion.
import numpy as np
def setup(a,b,phimax=4.0,nphi=1601):
    ph=np.linspace(-phimax,phimax,nphi); dp=ph[1]-ph[0]
    lr=-a*ph**2-b*ph**4
    return ph,dp,lr
def logz_k(lam,ph,dp,lr,k):  # log of int phi^k rho0 e^{lam phi}, lam complex array
    E=lr[None,:]+np.outer(lam,ph)
    mx=E.real.max(axis=1,keepdims=True)
    return np.log((np.exp(E-mx)*ph[None,:]**k).sum(1)*dp)+mx[:,0]
def kappa1(lam,ph,dp,lr):
    l0=logz_k(np.array([lam],complex),ph,dp,lr,0); l1=logz_k(np.array([lam],complex),ph,dp,lr,1)
    return np.exp(l1-l0).real[0]
def saddle(y,ph,dp,lr):
    lo,hi=-200.,200.
    for _ in range(80):
        mid=(lo+hi)/2
        if kappa1(mid,ph,dp,lr)<y: lo=mid
        else: hi=mid
    return (lo+hi)/2
def cond(N,ys,a,b,nom=401):
    """returns log p0(v) (density of sum of N iid rho0 at v=N y, up to const), sigma(y)=E[phi^2|M], tau3(y)=E[phi^3|M]"""
    ph,dp,lr=setup(a,b)
    out=[]
    for y in ys:
        l=saddle(y,ph,dp,lr)
        # width
        lam=np.array([l],complex)
        k2=np.exp(logz_k(lam,ph,dp,lr,2)-logz_k(lam,ph,dp,lr,0)).real[0]-y**2
        W=8/np.sqrt(N*k2)
        om=np.linspace(-W,W,nom); do=om[1]-om[0]
        lam=l+1j*om
        L0=logz_k(lam,ph,dp,lr,0); L2=logz_k(lam,ph,dp,lr,2); L3=logz_k(lam,ph,dp,lr,3)
        base=N*L0-lam*N*y
        sh=base.real.max()
        I0=(np.exp(base-sh)).sum()*do
        I2=(np.exp(base-sh+L2-L0)).sum()*do
        I3=(np.exp(base-sh+L3-L0)).sum()*do
        out.append((np.log(I0.real)+sh, (I2/I0).real, (I3/I0).real))
    return np.array(out)
