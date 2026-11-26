# Curie-Weiss phi^4: weight exp((J/2N)(sum phi)^2 - sum(a phi^2 + b phi^4)).  Exact via Hubbard-Stratonovich.
# z ~ exp(-N z^2/(2J)) Z1(z)^N  =>  z = (J/N) M + sqrt(J/N) g   (g std normal indep).
import numpy as np
from numpy.polynomial.legendre import leggauss
xg, wg = leggauss(400)
def Z1(z, a, b, k=0):
    # int phi^k exp(-a phi^2 - b phi^4 + z phi) dphi on [-R,R]
    R = 12.0/ (b**0.25) if b>0 else 12.0
    R = min(R, 60.0)
    ph = R*xg; w = R*wg
    z = np.atleast_1d(z)[:,None]
    e = -a*ph**2 - b*ph**4 + z*ph
    mx = e.max(axis=1, keepdims=True)
    return (w*ph**k*np.exp(e-mx)).sum(axis=1), mx[:,0]
def moments(a,b,J,N, nz=4001):
    # returns m2 = E Y^2, m4 = E Y^4, Y = M/N
    # find scale of z
    zmax = 0.0
    zs = np.linspace(-40,40,8001)
    v,mx = Z1(zs,a,b)
    f = N*(-zs**2/(2*J) + np.log(v)+mx)
    f -= f.max()
    keep = zs[f>-60]
    lo,hi = keep.min(), keep.max()
    zs = np.linspace(lo,hi,nz)
    v,mx = Z1(zs,a,b)
    f = N*(-zs**2/(2*J) + np.log(v)+mx); f-=f.max()
    w = np.exp(f); w/=w.sum()
    z2 = (w*zs**2).sum(); z4=(w*zs**4).sum()
    s = J/N
    M2 = (z2 - s)/s**2
    M4 = (z4 - 6*s**2*M2*s - 3*s**2)/s**4
    return M2/N**2, M4/N**4
if __name__=="__main__":
    for (a,b,J) in [(0.5,1,4),(2,0.1,4.6),(1.9,0.02,4),(1.0,0.5,4)]:
        for N in [64,256,1024]:
            m2,m4 = moments(a,b,J,N)
            B = m4/m2**2-3
            d=1e-4
            m2p,_=moments(a+d,b,J,N); m2m,_=moments(a-d,b,J,N)
            D = -(m2p-m2m)/(2*d)
            print(a,b,J,N,"m2=%.5f B=%.4f -da m2=%.4f  |B|/(b*(-da m2))=%.3f"%(m2,B,D,abs(B)/(b*D)))
