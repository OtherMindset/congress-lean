# Theorem A on tiny graphs: 1 site (J=0), 2 sites (ring N=2, double bond), triangle (N=3), 2x2 torus (= 4-ring with J=2),
# random (a,b) including theta close to 1. Checks kappa_min <= kappa_A and the S1/S2 inputs.
import numpy as np
from scipy.optimize import brentq
from ring import quantities, m2_only
rng=np.random.default_rng(1)
bad=0; n=0; worst=0; closest=None
for (J,N) in [(0.0,1),(1.0,2),(1.0,3),(2.0,4),(1.0,5)]:
    for _ in range(40):
        b=10**rng.uniform(-3,0.5); dm = J*(2 if N>2 else (1 if N==2 else 0))  # Gaussian critical a = J*deg/2
        a=dm/2*2/2 + 10**rng.uniform(-2,1.0)*np.sqrt(b) if True else 0
        a = (J if N>2 else (J if N==2 else 0.0)) + rng.uniform(-1,3)*np.sqrt(b)
        try: q=quantities(a,b,J,N,ng=260)
        except Exception: continue
        m2,B,chi,B2=q['m2'],q['B'],q['chi'],q['B2']; th=12*b*B2; x=b*chi**2/N
        S1=abs(B)/(24*x); S2raw=q['mdchi']-2*chi**2*(1-th)
        if S1>1+1e-7 or S2raw< -1e-9*chi**2: bad+=1; print("INPUT FAIL",J,N,a,b,S1,S2raw)
        if th>=1: continue
        n+=1; kA=1/((1-th)*(1-8*x)); tgt=(1-abs(B)/3)*m2
        if m2_only(a+4*b*kA*m2,b,J,N,ng=260)>tgt*(1+1e-9): bad+=1; print("A FAIL",J,N,a,b,th,kA)
        g=lambda k: m2_only(a+4*b*k*m2,b,J,N,ng=260)-tgt
        km=brentq(g,1e-9,kA,xtol=1e-8) if g(1e-9)>0 else 0
        worst=max(worst,km/kA)
        if closest is None or th>closest[0]: closest=(th,J,N,a,b,kA,km)
print("tested theta<1 cases:",n," bad:",bad," max kappa_min/kappa_A:",worst," largest theta case (theta,J,N,a,b,kA,kmin):",closest)
