import numpy as np
exec(open('ly1.py').read().split('def positive')[0])
y=np.linspace(0,60,60001); dy=y[1]-y[0]; X=np.linspace(0,25,1001)
def dens(a,beta):
    phi=np.exp(-beta*y**2)*np.prod(1-y[None,:]**2/a[:,None]**2,axis=0)
    wts=np.full_like(y,dy); wts[0]=dy/2
    return (np.cos(np.outer(X,y))*(phi*wts)).sum(1)/np.pi
a=np.array([1.08106799, 0.79553507, 0.53057452, 0.98220245, 1.21649303]); beta=0.8155727163214218
f=dens(a,beta); print('min density',f.min(),'max',f.max())
rng=np.random.default_rng(9); worst=-np.inf; cnt=0
import time; t0=time.time()
while time.time()-t0<80:
    n=rng.integers(1,5); a=rng.exponential(1,n)*rng.choice([0.5,1,2],n); beta=rng.exponential(1)*rng.choice([0.3,1,3])
    if beta*a.min()**2<0.05: continue
    f=dens(a,beta)
    if f.min()< -1e-9*f.max(): continue
    cnt+=1
    for H in np.geomspace(1e-2,20,25):
        T,k1=T_of(a,beta,H); r=T/abs(k1)**3*H**2
        if r>worst: worst=r; wa=(a,beta,H)
print(cnt,'positive LP worst',worst,wa)
