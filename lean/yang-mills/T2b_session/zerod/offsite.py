import numpy as np
x=np.linspace(-6,6,601); X,Y=np.meshgrid(x,x,indexing='ij')
def d(a,b,J,H):
    lw=-a*(X**2+Y**2)-b*(X**4+Y**4)+J*X*Y+H*(X+Y); w=np.exp(lw-lw.max()); w/=w.sum()
    E=lambda f:(w*f).sum(); Mc=X+Y-E(X+Y); xc=X-E(X); y2c=Y**2-E(Y**2)
    m=E(X); N=E(xc*y2c); return (m*E(xc*y2c*Mc)-N*E(xc*Mc))/(m*N)
w=(-np.inf,)
for a in [-2,-0.5,0.5,2]:
  for J in [0.3,1,3]:
    for H in [0.01,0.1,0.5,1.5]:
      v=d(a,1,J,H)
      if v>w[0]: w=(v,a,J,H)
print('off-site <phi0;phi1^2>/<phi0> worst rel derivative',w)
