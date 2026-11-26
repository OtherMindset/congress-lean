# Theorem 7.1 check on 2- and 3-site rings: R/2 = int Psi u sinh(eta u) P0 / int u sinh(eta u) P0
import numpy as np, psi_ring as P
def direct_R(N,a,b,J,H,ng=200,L=3.2):
    x,w=np.polynomial.legendre.leggauss(ng); x*=L; w*=L
    site=w*np.exp(-a*x**2-b*x**4+H*x)
    sq=np.sqrt(site); T=sq[:,None]*np.exp(J*np.outer(x,x))*sq[None,:]
    TN=np.linalg.matrix_power(T,N); d=np.diag(TN); Z=d.sum()
    m=(d*x).sum()/Z; return ((d*x**3).sum()/Z-m*(d*x**2).sum()/Z)/m
for (N,a,b,J) in ((2,-4.,1.,0.3),(3,-1.,0.5,0.6),(3,1.,0.3,0.5)):
    s,p,pe2,pe3=P.ring_fk(N,a,b,J,kmax=60.,nk=2401,ng=200)
    ds=s[1]-s[0]
    us=np.linspace(1e-3,s[-1]/np.sqrt(2)*1.4,1500); du=us[1]-us[0]
    A=[];PQ=[]
    for u in us:
        s2=np.sqrt(2)*u-s
        P2=np.interp(s2,s,p,left=0,right=0); E2=np.interp(s2,s,pe2,left=0,right=0); E3=np.interp(s2,s,pe3,left=0,right=0)
        A.append((N/(2*np.sqrt(2)))*np.sum(pe3*P2+p*E3-pe2*s2*P2/N-s*p*E2/N)*ds)
        PQ.append(np.sum(p*P2)*ds)
    A=np.array(A);PQ=np.array(PQ)  # A here = A(u)*density
    for H in (0.05,0.2,0.5):
        eta=np.sqrt(2)*H
        rhs=np.sum(A*np.sinh(eta*us))/np.sum(us*np.sinh(eta*us)*PQ)
        print(N,a,b,J,H,'R/2 direct=%.5f  sinh-rep=%.5f'%(direct_R(N,a,b,J,H)/2,rhs))
