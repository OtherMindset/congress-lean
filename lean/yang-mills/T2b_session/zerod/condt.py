# (B): for q-system with inhomogeneous quadratic a_x, uniform h: is <q0 qy^2>/<q0> nondecreasing in h (y=0,1)?
import numpy as np
x=np.linspace(-6,6,601); X,Y=np.meshgrid(x,x,indexing='ij')
def dd(a0,a1,b,J,h):
    lw=-a0*X**2-a1*Y**2-b*(X**4+Y**4)+J*X*Y+h*(X+Y); w=np.exp(lw-lw.max()); w/=w.sum()
    E=lambda f:(w*f).sum(); Mc=X+Y-E(X+Y); m=E(X); out=[]
    for F in (X**3, X*Y**2):
        N=E(F); out.append((E((F-N)*Mc)*m-N*E((X-m)*Mc))/(m*N))
    return out
worst=[np.inf,np.inf]; arg=[None,None]
for a0 in [-1,0.5,2,6]:
  for a1 in [-1,0.5,2,6]:
    for J in [0.3,1,3]:
      for h in [0.01,0.1,0.5,1.5]:
        v=dd(a0,a1,0.5,J,h)
        for i in range(2):
          if v[i]<worst[i]: worst[i]=v[i]; arg[i]=(a0,a1,J,h)
print('min rel derivative of <q0^3>/<q0>:',worst[0],arg[0]); print('min rel derivative of <q0 q1^2>/<q0>:',worst[1],arg[1])
