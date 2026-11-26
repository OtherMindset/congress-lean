# Test Theorem A ingredients and conclusion on rings (J=1) exactly.
import numpy as np, sys
from ringtm import quantities, m2_only
from scipy.optimize import brentq
def kmin(a,b,J,N,m2,B):
    tgt=(1-abs(B)/3)*m2
    g=lambda k: m2_only(a+4*b*k*m2,b,J,N)-tgt
    if g(1e-9)<=0: return 0.0
    hi=1.0
    while g(hi)>0:
        hi*=2
        if hi>1e3: return np.inf
    return brentq(g,1e-9,hi,xtol=1e-7)
def kappaA(theta,x):
    if theta>=1: return np.inf
    g=1-theta
    c=[]
    if 8*x<1: c.append(1/(g*(1-8*x)))
    if x>0: c.append(1/(4*g*x))
    return min(c)
print("# a b N | m2 B chi B2 | S1:|B|/(24b chi^2/N) S2:(-dchi)/(2chi^2(1-12bB2)) | theta x kappaA kappamin")
J=1.0
bad=0
for b in [0.5,0.1,0.02,0.005]:
  for N in [4,16,64]:
    for a in [3.0,2.0,1.5,1.2,1.0,0.8,0.5,0.0,-1.0]:
        q=quantities(a,b,J,N)
        m2,B,chi,B2=q['m2'],q['B'],q['chi'],q['B2']
        h=1e-4
        dchi=-(quantities(a+h,b,J,N)['chi']-quantities(a-h,b,J,N)['chi'])/(2*h)
        S1=abs(B)/(24*b*chi**2/N)
        S2=dchi/(2*chi**2*(1-12*b*B2)) if 12*b*B2<1 else np.nan
        theta=12*b*B2; x=b*chi**2/N
        kA=kappaA(theta,x)
        km=kmin(a,b,J,N,m2,B)
        flag=""
        if S1>1+1e-6: flag+=" S1FAIL"
        if S2==S2 and S2<1-1e-6: flag+=" S2FAIL"
        if km>kA+1e-6: flag+=" AFAIL"
        if flag: bad+=1
        print("%5.2f %5.3f %3d | %.4g %.4f %.4g %.4g | %.4f %s | %.4f %.4g %.4f %.4f%s"%(a,b,N,m2,B,chi,B2,S1,("%.4f"%S2) if S2==S2 else "  -   ",theta,x,kA,km,flag))
        sys.stdout.flush()
print("bad",bad)
