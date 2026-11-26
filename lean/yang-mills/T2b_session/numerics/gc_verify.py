"""Independent mpmath verification of a GC violation: compute E_pi_h[1_D] = <q0 1_D(r)>/<q0>
directly by enumeration of (s, r) in high precision at h and h+-delta, plus exact derivative."""
import mpmath as mp, itertools, json, sys

def ratio(v, f, J, h, Dset, dps=40):
    mp.mp.dps = dps
    n = len(v); k = len(v[0])
    num = mp.mpf(0); den = mp.mpf(0); dnum = mp.mpf(0); dden = mp.mpf(0)
    for l in itertools.product(range(k), repeat=n):
        r = [mp.mpf(v[x][l[x]]) for x in range(n)]
        lr = sum(mp.mpf(f[x][l[x]]) for x in range(n))
        inD = tuple(l) in Dset
        for s in itertools.product([-1, 1], repeat=n):
            q = [s[x]*r[x] for x in range(n)]
            E = lr + sum(mp.mpf(J[x][y])*q[x]*q[y] for x in range(n) for y in range(x+1, n)) + h*sum(q)
            w = mp.exp(E)
            Q = sum(q)
            den += q[0]*w; dden += q[0]*Q*w
            if inD:
                num += q[0]*w; dnum += q[0]*Q*w
    val = num/den
    deriv = (dnum*den - num*dden)/den**2
    return val, deriv

if __name__ == "__main__":
    d = json.load(open(sys.argv[1]))
    w = d['worst'] if 'worst' in d else d
    D = set(tuple(x) for x in w['D'])
    h = mp.mpf(w['h'])
    for dps in (30, 50):
        val, der = ratio(w['v'], w['f'], w['J'], h, D, dps)
        print("dps", dps, "E[1_D] =", mp.nstr(val, 20), " d/dh =", mp.nstr(der, 20))
    dl = mp.mpf('1e-6')
    a, _ = ratio(w['v'], w['f'], w['J'], h-dl, D); b, _ = ratio(w['v'], w['f'], w['J'], h+dl, D)
    print("central FD:", mp.nstr((b-a)/(2*dl), 15))
    for hh in ['0.0001', '0.001', '0.01', '0.1', '0.3', '1', '3']:
        val, der = ratio(w['v'], w['f'], w['J'], mp.mpf(hh), D)
        print(" h=%s  E=%s  d/dh=%s" % (hh, mp.nstr(val, 12), mp.nstr(der, 6)))
