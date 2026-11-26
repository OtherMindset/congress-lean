import numpy as np
exec(open('ly1.py').read().split('def positive')[0])
rng=np.random.default_rng(5); worst=-np.inf; cnt=0
Hg=np.geomspace(1e-3,1e3,400)
for t in range(100000):
    n=rng.integers(1,6); a=rng.exponential(1,n)*rng.choice([0.3,1,3],n); beta=rng.choice([0,rng.exponential(1)*rng.choice([0.1,1,10])])
    w=a[:,None]**2+Hg**2; v=1/w; y=Hg**2*v
    k2=2*beta+(v*(2-4*y)).sum(0)
    if k2.min()<=0: continue
    cnt+=1
    for H in np.geomspace(1e-2,30,25):
        T,k1=T_of(a,beta,H); r=T/abs(k1)**3*H**2
        if r>worst: worst=r; wa=(a,beta,H)
print(cnt,'worst among log-convex LP',worst,wa)
