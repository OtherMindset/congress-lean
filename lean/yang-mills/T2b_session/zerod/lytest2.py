import numpy as np
from numpy.polynomial import polynomial as P
rng=np.random.default_rng(7)
def R(vals,wts,H):
    lw=H*vals; w=wts*np.exp(lw-lw.max()); w/=w.sum()
    m1,m2,m3=[(w*vals**k).sum() for k in (1,2,3)]; return (m3-m1*m2)/m1
Hs=np.linspace(2e-3,3,600); worst=-1; npos=0
for trial in range(20000):
    n=rng.integers(1,7); th=rng.uniform(0,np.pi,n)
    # prod (z + 1/z - 2cos th)/2 in z=e^{2H} -> Laurent poly; multiply by z^n
    c=np.array([1.])
    for t in th: c=P.polymul(c,[0.5,-np.cos(t),0.5])
    if c.min()<-1e-14: continue
    npos+=1
    vals=2*(np.arange(len(c))-n).astype(float); wts=np.maximum(c,0)
    Rs=np.array([R(vals,wts,H) for H in Hs]); d=np.diff(Rs)/(np.abs(Rs).max()+1e-12)
    if d.max()>worst: worst=d.max(); print(trial,n,np.round(th,3),worst,flush=True)
print('positive cases',npos)
