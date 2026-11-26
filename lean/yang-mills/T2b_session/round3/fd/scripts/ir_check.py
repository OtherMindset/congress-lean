# Check infrared bound Ghat(k) <= 1/(J*2(1-cos k)) on even rings, and B2 monotone in a (GKS), and the
# IR-derived bound on 12 b B2.
import numpy as np
from ringtm import quantities
worst=0; worstmono=-1
for b in [0.5,0.1,0.02]:
  for N in [4,8,16,32]:
    prevB2=None
    for a in [-1.0,0.0,0.5,0.8,1.0,1.2,1.5,2.0,3.0]:
        q=quantities(a,b,1.0,N); G=q['G']
        k=2*np.pi*np.arange(1,N)/N
        Gh=np.array([ (G*np.cos(kk*np.arange(N))).sum() for kk in k])
        r=(Gh*2*(1-np.cos(k))).max()
        worst=max(worst,r)
        if prevB2 is not None: worstmono=max(worstmono,q['B2']/prevB2)
        prevB2=q['B2']
print("max Ghat(k)*E(k) over all cases (IR bound says <=1):",worst)
print("max B2(a_next)/B2(a_prev) for increasing a (GKS says <=1):",worstmono)
