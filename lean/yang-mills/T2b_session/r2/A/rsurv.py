# CW phi^4: surviving fraction r = S / N Cov(Y^2,Y),  S=-d_a m = N Cov(sigma(Y),Y), N Cov(Y^2,Y)=2 m chi + chi'/N.
# Also the target ratio for (Sigma_theta): (m - H chi)/S.
import sys; sys.path.insert(0,'/home/claude/t2b/theta1')
import numpy as np
from cw_theta import site, obs
for (a,b,J) in [(0.5,1.0,4.0),(1.9,0.02,4.0),(2.0,0.1,4.0)]:
  W=J*6+4; S0=site(a,b,W+2)
  for N in [64,1024]:
    print(f"a={a} b={b} J={J} N={N}")
    for h in [1e-5,1e-4,1e-3,3e-3,1e-2,3e-2,1e-1,1.0]:
        dh=h*1e-3
        m,chi,S,_,_=obs(S0,J,N,h,W)
        cp=obs(S0,J,N,h+dh,W)[1]; cm=obs(S0,J,N,h-dh,W)[1]
        zm=2*m*chi+(cp-cm)/(2*dh)/N
        print(f"  h={h:.0e} m={m:.4f} chi={chi:.4g} S={S:.4g} zeromode={zm:.4g} r={S/zm:.3f} (m-hchi)/S={(m-h*chi)/S:.3g}")
