import numpy as np
exec(open('psiQphi4.py').read().split('vs=np.linspace')[0])
vs=np.linspace(0.1,5,25)
for a,J in [(-4,0.0),(-4,0.2),(-4,1.0),(-4,3.0),(-2,0.0),(-2,0.1),(-2,0.5),(2,1.0),(2.05,1.9)]:
    p=psi_curve(a,1,J,vs,L=4.0,n=100); d=np.diff(p).max()/np.abs(p).max()
    print(a,J,'max rel incr',round(d,4),np.round(p[::4],3),flush=True)
