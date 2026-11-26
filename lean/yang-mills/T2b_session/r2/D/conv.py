import sys; sys.path.insert(0,'/home/claude/t2b/theta1')
import numpy as np, mpmath as mp
from cw_theta import site, obs
mp.mp.dps=25
# one site: d^2 m/da^2 = <phi;phi^2;phi^2>
def k3(a,b,H):
    w=lambda x: mp.exp(-a*x**2-b*x**4+H*x)
    I=lambda f: mp.quad(lambda x:f(x)*w(x),[-mp.inf,-2,0,2,mp.inf])
    Z=I(lambda x:1); E=lambda f:I(f)/Z
    m=E(lambda x:x); q=E(lambda x:x**2)
    return E(lambda x:(x-m)*(x**2-q)**2)
for p in [(1,1,0.3),(2,0.02,0.5),(-2,1,0.3),(-2,1,2),(-4,1,1)]:
    print("one site",p," <phi;phi^2;phi^2> =",mp.nstr(k3(*p),6))
# CW: second a-derivative of m at fixed h (uniform mass direction)
b,J,N=1.0,4.0,256; W=J*6+4
for a0 in [0.4,0.6]:
  chi0=obs(site(a0,b,W+2),J,N,1e-8,W)[1]
  for x in [0.1,0.3,1.0,3.0]:
    h=x/chi0; da=0.01
    ms=[obs(site(a0+k*da,b,W+2),J,N,h,W)[0] for k in (-1,0,1)]
    print(f"CW a0={a0} N={N} h={h:.3g} (h*chi0={x}) m={ms[1]:.4f}  d2m/da2={(ms[0]-2*ms[1]+ms[2])/da**2:.4g}")
