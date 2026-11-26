# One site: test  <phi^4>_a >= 3 <phi^2>_a <phi^2>_{a+4b kappa <phi^2>_a};  minimal kappa (b=1 wlog by scaling)
import numpy as np
from mpmath import mp, quad, exp, mpf, findroot, inf
mp.dps=30
def mom(a,k,b=1):
    f=lambda x: x**k*exp(-a*x*x-b*x**4)
    return 2*quad(f,[0,1,3,6,inf])
def m2(a): return mom(a,2)/mom(a,0)
def m4(a): return mom(a,4)/mom(a,0)
worst=0
for a in [-30,-20,-10,-6,-4,-3,-2,-1,-0.5,0,0.5,1,2,5,10,30,100]:
    a=mpf(a); x2=m2(a); x4=m4(a); tgt=x4/(3*x2)
    g=lambda k: m2(a+4*k*x2)-tgt
    # bisection
    lo,hi=mpf(0),mpf(1)
    while g(hi)>0: hi*=2
    for _ in range(60):
        mid=(lo+hi)/2
        if g(mid)>0: lo=mid
        else: hi=mid
    # third cumulant of phi^2 (convexity of <phi^2> in a)
    x6=mom(a,6)/mom(a,0)
    k3=x6-3*x4*x2+2*x2**3
    print("a=%7.2f  kappa_min=%.5f  B=%.4f  kappa3(phi^2)=%.3e"%(a,hi,x4/x2**2-3,k3))
