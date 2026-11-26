# CW phi^4: sign of d_a chi (Griffiths-III-type "chi decreasing in mass") at h>0, flip regime.
import sys; sys.path.insert(0,'/home/claude/t2b/theta1')
import numpy as np
from cw_theta import site, obs
b,J=1.0,4.0
for a0 in [0.5]:
  for N in [64,1024]:
    da=1e-3; W=J*6+4
    Sp=site(a0+da,b,W+2); Sm=site(a0-da,b,W+2); S0=site(a0,b,W+2)
    print(f"a={a0} b={b} J={J} N={N}")
    for h in [1e-5,1e-4,3e-4,1e-3,3e-3,1e-2,3e-2,1e-1]:
        m0,c0,dam,_,_=obs(S0,J,N,h,W)
        cp=obs(Sp,J,N,h,W)[1]; cm=obs(Sm,J,N,h,W)[1]
        print(f"  h={h:.0e} m={m0:.4f} x=N*m*h={N*m0*h:.3f} chi={c0:.4g}  -d_a chi={-(cp-cm)/(2*da):+.4g}  -d_a m={dam:.4g}")
