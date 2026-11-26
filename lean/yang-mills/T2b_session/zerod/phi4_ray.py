import numpy as np
x=np.linspace(-6,6,601); X,Y=np.meshgrid(x,x,indexing='ij')
def dRray(a,b,J,c0,c1,H):
    lw=-a*(X**2+Y**2)-b*(X**4+Y**4)+J*X*Y+H*(c0*X+c1*Y); w=np.exp(lw-lw.max()); w/=w.sum()
    E=lambda f:(w*f).sum(); D=c0*X+c1*Y; Dc=D-E(D); xc=X-E(X); x2c=X**2-E(X**2)
    m=E(X); N=E(xc*x2c); return (m*E(xc*x2c*Dc)-N*E(xc*Dc))/(m*N)
w=(-np.inf,)
for a in [-2,-0.5,0.5,2]:
  for J in [0.3,1,3]:
    for c1 in [0,0.2,0.5,2,5,20]:
      for H in [0.01,0.05,0.2,0.8]:
        v=dRray(a,1,J,1,c1,H)
        if v>w[0]: w=(v,a,J,c1,H)
print('ray worst',w)
