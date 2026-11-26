# FD-P0 test in Curie-Weiss: minimal kappa with m2(a+4 b kappa m2(a)) <= m4(a)/(3 m2(a))
import numpy as np, sys
from cw import moments
from scipy.optimize import brentq
def kmin(a,b,J,N):
    m2,m4 = moments(a,b,J,N)
    target = m4/(3*m2)
    g = lambda k: moments(a+4*b*k*m2,b,J,N)[0]-target
    if g(1e-6)<=0: return 0.0, m2, m4/m2**2-3
    hi=1.0
    while g(hi)>0:
        hi*=2
        if hi>1e4: return np.inf, m2, m4/m2**2-3
    return brentq(g,1e-6,hi,xtol=1e-6), m2, m4/m2**2-3
for (b,J) in [(1,4),(0.1,4),(0.02,4),(0.005,4)]:
    # critical a: mean-field  J*<phi^2>_1site = 1  -> find a_c
    from cw import Z1
    def crit(a):
        z0,_=Z1(0.0,a,b); z2,_=Z1(0.0,a,b,2); return J*z2[0]/z0[0]-1
    ac = brentq(crit,-5,J)
    print("b=%g J=%g a_c=%.4f"%(b,J,ac))
    for N in [64,1024,16384]:
        row=[]
        for da in [-0.5,-0.2,-0.05,-0.01,0,0.01,0.05,0.2,0.5,2.0]:
            a = ac+da*max(b,0.05)**0.5
            k,m2,B = kmin(a,b,J,N)
            row.append("%.3f(B%.2f)"%(k,B))
        print("  N=%5d"%N," ".join(row))
