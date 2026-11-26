import numpy as np
x=np.linspace(-6,6,601); X,Y=np.meshgrid(x,x,indexing='ij')
def dR(a,b,J,h0,h1,H):
    lw=-a*(X**2+Y**2)-b*(X**4+Y**4)+J*X*Y+(H+h0)*X+(H+h1)*Y; w=np.exp(lw-lw.max()); w/=w.sum()
    E=lambda f:(w*f).sum(); Mc=X+Y-E(X+Y); xc=X-E(X); x2c=X**2-E(X**2)
    m=E(X); N=E(xc*x2c); return (m*E(xc*x2c*Mc)-N*E(xc*Mc))/(m*N), N/m
worst=(-np.inf,)
for a in [-2,-0.5,0.5,2]:
  for J in [0.3,1,3]:
    for h1 in [0,0.5,2,5]:
      for h0 in [0,0.5,2]:
        for H in [0.01,0.1,0.5,1.5]:
          v,R=dR(a,1,J,h0,h1,H)
          if v>worst[0]: worst=(v,a,J,h0,h1,H,R)
print('worst rel dR/R',worst)
x=np.linspace(-6,6,1201); X,Y=np.meshgrid(x,x,indexing='ij')
print('fine grid nonuniform point', dR(-2,1,3,0,0.5,0.01), dR(-2,1,3,0,0.5,0.05), dR(-2,1,3,0,0.5,0.3))
w2=-np.inf
for a in [-2,-0.5,0.5,2]:
  for J in [0.3,1,3]:
    for H in [0.01,0.05,0.1,0.5,1.5]:
      v,_=dR(a,1,J,0,0,H); w2=max(w2,v)
print('uniform worst',w2)
