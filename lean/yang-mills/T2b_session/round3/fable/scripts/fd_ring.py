import numpy as np
from ring import mom
from scipy.optimize import brentq
def kmin(a,b,J,N):
    m2,m4=mom(a,b,J,N); tgt=m4/(3*m2); B=m4/m2**2-3
    g=lambda k: mom(a+4*b*k*m2,b,J,N)[0]-tgt
    hi=1.0
    while g(hi)>0:
        hi*=2
        if hi>64: return np.inf,m2,B
    return brentq(g,1e-9,hi,xtol=1e-5),m2,B
rng=np.random.default_rng(1)
worst=0
print("# a b J N kappa_min 1-|B|/3 m2 B")
cases=[]
for J in [1.0]:
  for b in [0.5,0.1,0.02]:
    for a in [1.2,1.0,0.9,0.7,0.5,0.0,-1.0,-3.0]:
      for N in [4,16,64]:
        cases.append((a,b,J,N))
for (a,b,J,N) in cases:
    try:
        k,m2,B=kmin(a,b,J,N)
    except Exception as e:
        print(a,b,J,N,"ERR",e); continue
    worst=max(worst,k)
    print("%5.2f %5.2f %3.1f %3d  kmin=%.4f  SCbound=%.4f  m2=%.4g B=%.3f"%(a,b,J,N,k,1-abs(B)/3,m2,B))
print("worst",worst)
