import numpy as np
exec(open('phi4_2site.py').read().split("worst=(-np.inf,)")[0])
for lab,cond in [('h0>h1',lambda h0,h1:h0>h1),('h1>h0',lambda h0,h1:h1>h0)]:
    w=(-np.inf,)
    for a in [-2,0.5]:
      for J in [0.3,3]:
        for h0 in [0,0.5,2]:
          for h1 in [0,0.5,2]:
            if not cond(h0,h1): continue
            for H in [0.01,0.1,0.5]:
              v,_=dR(a,1,J,h0,h1,H)
              if v>w[0]: w=(v,a,J,h0,h1,H)
    print(lab,w)
