# (O6) pointwise monotonicity of Psi(u)=E_0[sum q t^2 | Q=u]/u on rings, a=-4,b=1,J=0.3
# Uses independence of copies: given M1=sum phi, M2=sum phi', copies independent.
# E[sum_x q_x t_x^2 | M1=s1,M2=s2] = N/(2 sqrt2) [e3(s1)+e3(s2) - e2(s1) s2/N - s1 e2(s2)/N]
import numpy as np, sys
def ring_fk(N,a,b,J,ng=160,L=3.2,nk=1601,kmax=40.0,ns=1201,smax=None):
    x,w=np.polynomial.legendre.leggauss(ng); x*=L; w*=L
    site=w*np.exp(-a*x**2-b*x**4)
    nb = 1 if N==2 else N  # bonds
    Jeff = J if N>2 else J  # 2-ring: single bond
    if smax is None: smax=N*L*0.75
    ks=np.linspace(-kmax,kmax,nk); dk=ks[1]-ks[0]
    s=np.linspace(-smax,smax,ns)
    out={}
    phis=[]
    for k in ks:
        sq=np.sqrt(site)*np.exp(0.5j*k*x)
        T=sq[:,None]*np.exp(Jeff*np.outer(x,x))*sq[None,:]
        if N==1:
            TN=np.diag(sq*sq)
        else:
            TN=np.linalg.matrix_power(T,N)
        d=np.diag(TN)
        phis.append([d.sum(),(d*x**2).sum(),(d*x**3).sum()])
    phis=np.array(phis)  # characteristic fns (unnormalised)
    Z=phis[nk//2,0].real
    # inverse Fourier: f(s)=1/2pi int e^{-iks} phi(k) dk  (trapezoid with window)
    win=np.exp(-0.5*(ks/(kmax/3.5))**2)  # mild Gaussian smoothing to suppress truncation ringing
    E=np.exp(-1j*np.outer(s,ks))
    f=(E@(phis*win[:,None])).real*dk/(2*np.pi)/Z
    return s,f[:,0],f[:,1],f[:,2]  # p(s), p e2, p e3
def psi(N,a,b,J,us):
    s,p,pe2,pe3=ring_fk(N,a,b,J)
    ds=s[1]-s[0]
    res=[]
    for u in us:
        s2=np.sqrt(2)*u - s
        P2=np.interp(s2,s,p,left=0,right=0); E2=np.interp(s2,s,pe2,left=0,right=0); E3=np.interp(s2,s,pe3,left=0,right=0)
        num=(N/(2*np.sqrt(2)))*np.sum(pe3*P2+p*E3-pe2*s2*P2/N-s*p*E2/N)*ds
        den=np.sum(p*P2)*ds
        res.append(num/den/u)
    return np.array(res)
if __name__=="__main__":
  a,b,J=-4.0,1.0,0.3
  for N in range(1,9):
      us=np.linspace(0.05,1.2*N,60)
      ps=psi(N,a,b,J,us)
      inc=np.diff(ps)
      i=np.argmax(inc)
      print('N=%d  max increase of Psi over grid: %+.4g at u~%.2f ; Psi range [%.4f,%.4f]; any increase: %s'%(N,inc.max(),us[i],ps.min(),ps.max(),(inc>1e-6).any()))
      sys.stdout.flush()
