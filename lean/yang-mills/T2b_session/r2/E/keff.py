import numpy as np, sys
from chain import mchain, extent
rng=np.random.default_rng(7); rows=[]
for J0 in ['site','chain']:
  for i in range(200):
    a=rng.uniform(-4,4); b=np.exp(rng.uniform(np.log(.02),np.log(2))); J=0.0 if J0=='site' else np.exp(rng.uniform(np.log(.1),np.log(3))); H=np.exp(rng.uniform(np.log(.01),np.log(3)))
    L=extent(a,b,J,H)
    f=lambda x: mchain(x,b,J,H,160,L)
    d=0.01; slope=-(f(a+d)-f(a-d))/(2*d)
    if slope<=0: continue
    best=0;bd=0
    for D in [0.03,0.1,0.3,1,3]:
        K=(f(a)-f(a+D))/(D*slope)
        if K>best: best,bd=K,D
    rows.append((J0=='chain',a,b,J,H,best,bd))
r=np.array(rows)
for c in (0,1):
    s=r[r[:,0]==c]; i=np.argmax(s[:,5]); print('chain' if c else 'site', 'n',len(s),'max K',s[i,5],'at',s[i,1:5],'Delta',s[i,6],' frac K>1',(s[:,5]>1+1e-9).mean())
