import numpy as np, psi_ring as P
import importlib
a,b,J=-4.0,1.0,0.3
us=np.linspace(1.0,3.0,21)
for N in (2,4,8):
  for (kmax,nk,ng) in ((40.,1601,160),(60.,2401,220)):
    s,p,pe2,pe3=P.ring_fk(N,a,b,J,ng=ng,kmax=kmax,nk=nk)
    def psi(u):
        ds=s[1]-s[0]; s2=np.sqrt(2)*u-s
        P2=np.interp(s2,s,p,left=0,right=0); E2=np.interp(s2,s,pe2,left=0,right=0); E3=np.interp(s2,s,pe3,left=0,right=0)
        num=(N/(2*np.sqrt(2)))*np.sum(pe3*P2+p*E3-pe2*s2*P2/N-s*p*E2/N)*ds
        return num/(np.sum(p*P2)*ds)/u
    v=np.array([psi(u) for u in us])
    print(N,kmax,' '.join('%.4f'%t for t in v))
