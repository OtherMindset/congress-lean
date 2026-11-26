from mpmath import mp, mpf, exp
import itertools, numpy as np
mp.dps=40
Jm=[[0,0.0557,0,1.305],[0,0,0.8211,0.1426],[0,0,0,0.0456],[0,0,0,0]]
c=[1,1,1,0.8705]; H0=mpf('0.10454804606162331')
J={(a,b):mpf(Jm[a][b]) for a in range(4) for b in range(a+1,4) if Jm[a][b]}
S=list(itertools.product([1,-1],repeat=4))
def P(g):
    h=[H0*mpf(x) for x in c]; h[3]=mpf(g)
    w=lambda s: exp(sum(J[e]*s[e[0]]*s[e[1]] for e in J)+sum(h[i]*s[i] for i in range(4)))
    Z=sum(w(s) for s in S); m=lambda f: sum(w(s)*f(s) for s in S)/Z
    t3=m(lambda s:s[0]*s[1]*s[2])
    return (1+0*t3, (m(lambda s:s[0])*m(lambda s:s[1]*s[2])+m(lambda s:s[1])*m(lambda s:s[0]*s[2])+m(lambda s:s[2])*m(lambda s:s[0]*s[1]))/t3)[1]
for g in np.logspace(-1.5,1.3,50)[[8,9,10,11,12,13,14]]: print(float(g),P(mpf(float(g))))
# P4 and the ray at the same c
