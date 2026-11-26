import numpy as np
exec(open('condt.py').read().split('worst=')[0])
worst=[np.inf,np.inf]; arg=[None,None]
for a0 in [-6,-4,-2,0]:
  for a1 in [-6,-4,-2,0,3]:
    for J in [0.02,0.1,0.5]:
      for h in [0.01,0.05,0.2,0.6]:
        v=dd(a0,a1,1.0,J,h)
        for i in range(2):
          if v[i]<worst[i]: worst[i]=v[i]; arg[i]=(a0,a1,J,h)
print('deep wells: min rel d <q0^3>/<q0>:',worst[0],arg[0]); print('min rel d <q0 q1^2>/<q0>:',worst[1],arg[1])
