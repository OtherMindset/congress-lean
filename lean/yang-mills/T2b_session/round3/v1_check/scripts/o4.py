# (O4) two sites, a=-2,b=1,J=3, extra field 0.5 on one site, uniform H=0.01
import numpy as np
def stats(a,b,J,h0,h1,ng=1201,L=4.0):
    x,w=np.polynomial.legendre.leggauss(ng); x=x*L; w=w*L
    X0,X1=np.meshgrid(x,x,indexing='ij'); W=np.outer(w,w)
    E=J*X0*X1+h0*X0+h1*X1-a*(X0**2+X1**2)-b*(X0**4+X1**4)
    P=W*np.exp(E-E.max()); P/=P.sum()
    ex=lambda f:(P*f).sum()
    m0=ex(X0); R0=(ex(X0**3)-m0*ex(X0**2))/m0
    m1=ex(X1); R1=(ex(X1**3)-m1*ex(X1**2))/m1
    return R0,R1,ex(X0**2),ex(X1**2)
a,b,J,H,he=-2,1,3,0.01,0.5
for ng in (601,1201):
  d=1e-4
  for site in (0,1):  # extra field on site 'site'
    def f(Hu):
        hh=[Hu,Hu]; hh[site]+=he
        return stats(a,b,J,hh[0],hh[1],ng)
    p=f(H+d); q=f(H-d); c=f(H)
    for obs in (0,1):
        dR=(p[obs]-q[obs])/(2*d); dQ=(p[2+obs]-q[2+obs])/(2*d)
        print(ng,'extra field on site',site,'R at site',obs,'R=%.4f dR/dH=%.4f (dR/dH)/R=%+.4f  dR/dH/d<phi^2>/dH=%+.4f'%(c[obs],dR,dR/c[obs],dR/dQ))
