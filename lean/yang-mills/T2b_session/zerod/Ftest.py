# 2-site phi^4 ferromagnet: is H -> <q0 F(|q0|,|q1|)>/<q0> nonincreasing for F coordinatewise decreasing?
import numpy as np
x=np.linspace(-5,5,401); X,Y=np.meshgrid(x,x,indexing='ij')
def ratio(a,b,J,H,F):
    lw=-a*(X**2+Y**2)-b*(X**4+Y**4)+J*X*Y+H*(X+Y); w=np.exp(lw-lw.max())
    return (w*X*F).sum()/(w*X).sum()
Fs={'exp(-q1^2)':np.exp(-Y**2),'1[|q1|<0.5]':(abs(Y)<0.5)*1.0,'exp(-q0^2)':np.exp(-X**2),
    '1[|q1|<1.5]':(abs(Y)<1.5)*1.0,'1/(1+q0^2+q1^2)':1/(1+X**2+Y**2)}
worst={}
for a in [-2,-0.5,0.5,2]:
  for J in [0.2,1,3]:
    for name,F in Fs.items():
      Hs=np.linspace(0.02,4,40); rs=[ratio(a,1,J,H,F) for H in Hs]; d=np.diff(rs).max()
      if d>worst.get(name,(-1,))[0]: worst[name]=(d,a,J,Hs[np.argmax(np.diff(rs))])
for k,v in worst.items(): print(k,v)
