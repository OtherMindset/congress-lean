from mpmath import mp, mpf, exp
import itertools
mp.dps = 40
J = {(0,1): mpf('0.06'), (1,2): mpf('1.7')}
def S(h):
    Z = 0; m = [0,0,0]; pr = {}; t3 = 0
    for c in itertools.product([-1,1], repeat=3):
        w = exp(sum(v*c[a]*c[b] for (a,b),v in J.items()) + sum(h[i]*c[i] for i in range(3)))
        Z += w; t3 += w*c[0]*c[1]*c[2]
        for i in range(3): m[i] += w*c[i]
        for a,b in [(1,2),(0,2),(0,1)]: pr[(a,b)] = pr.get((a,b),0) + w*c[a]*c[b]
    m = [x/Z for x in m]; t3 /= Z; pr = {k:v/Z for k,v in pr.items()}
    return (m[0]*pr[(1,2)] + m[1]*pr[(0,2)] + m[2]*pr[(0,1)])/t3
h0 = [mpf('0.001'), mpf('0.002'), mpf('0.002')]
d = mpf('1e-12')
for x in range(3):
    h1 = list(h0); h1[x] += d
    print("dS/dh_%d ="%x, (S(h1)-S(h0))/d)
print("S =", S(h0))
for t in [1, 2, 5, 10, 100]:
    print("ray t=",t, S([v*t for v in h0]))
