from mpmath import mp, mpf, exp, tanh, cosh
import itertools
mp.dps=50
# isolated sites 0,1 with fields a0,a1; site 2 coupled to 3,4
def P4(H):
    hb=[mpf('1.49276554'),mpf('1.64976646'),mpf('0.73583172'),mpf('2.27924716'),mpf('2.05455999')]
    J={(2,4):mpf('0.14228939'),(3,4):mpf('0.04044185')}
    S=list(itertools.product([1,-1],repeat=5))
    w=lambda s: exp(sum(J[e]*s[e[0]]*s[e[1]] for e in J)+H*sum(hb[i]*s[i] for i in range(5)))
    Z=sum(w(s) for s in S); m=lambda f: sum(w(s)*f(s) for s in S)/Z
    t3=m(lambda s:s[0]*s[1]*s[2])
    return (m(lambda s:s[0])*m(lambda s:s[1]*s[2])+m(lambda s:s[1])*m(lambda s:s[0]*s[2])+m(lambda s:s[2])*m(lambda s:s[0]*s[1]))/t3
import numpy as np
prev=None;worst=0
for H in np.logspace(-3,1.3,80):
    v=P4(mpf(float(H)))
    if prev is not None and v<prev: worst=max(worst,prev-v)
    prev=v
print("worst decrease (mp):",worst)
