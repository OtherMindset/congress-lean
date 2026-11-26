# IR bound Ghat(k) <= 1/E(k), E = 2(1-cos k), on phi^4 rings (J=1); even and odd N. Also Lebowitz B<=0.
import numpy as np
from ring import quantities
worst={}; maxB=-9
for b in [0.5,0.1,0.02]:
  for N in [4,5,7,8,9,16,32]:
    for a in [-1.0,0.0,0.5,0.8,1.0,1.2,1.5,2.0,3.0]:
        q=quantities(a,b,1.0,N); G=q['G']; maxB=max(maxB,q['B'])
        k=2*np.pi*np.arange(1,N)/N
        Gh=np.array([(G*np.cos(kk*np.arange(N))).sum() for kk in k])
        r=(Gh*2*(1-np.cos(k))).max()
        key='even' if N%2==0 else 'odd'; worst[key]=max(worst.get(key,0),r)
print("max Ghat(k)E(k):",worst,"  max B:",maxB)
