# Numerical test (evidence, not proof) of the identity behind the G certificates:
#   is the expression (*) of the header of python/yang-mills/S4_general_d/G_box_A_1of2.py (repeated in the
#   S6 README, "Arithmetic rules"),  (*) = U(s2) - U(s1) + q (m_{s2} - m_{s1})^2/(2d),
#   equal to d^2 W/d mu^2 for  W(mu,r,d) = (1/2) int_{-1}^{1} |q_{s2}(x) - q_{s1}(x)| dx,
#   q_s(x) = e^{sx} nu_r(x)/Z(s), Z(s) = int_{-1}^{1} e^{sx} nu_r, nu_r(x) = w phi(r w), w = sqrt(1-x^2),
#   phi(z) = sinh(z)/z, s1 = mu - d, s2 = mu + d ?
# SIDE A (functions W, d2W) uses the definition of W only: Z by quadrature; the crossing point as a
#   numerical root of q_{s2} - q_{s1} (bisection, then secant; no closed form); the integral of
#   |q_{s2} - q_{s1}| split at that root; then d^2/dmu^2 by the five-point stencil at steps H, H/2, H/4
#   with two Richardson steps (errors h^4 and h^6 removed).
# SIDE B (function header_star) evaluates the header's definitions by quadrature: the thing under test.
# The two sides share only nu, the quadrature rule and mpmath.
# Quadrature: x = sin(t), Gauss-Legendre with NG nodes in t (integrands entire in t on each piece).
# THRESHOLD, fixed before the first run: max |A - B|/|B| over all sample points < 1e-10.
# Also: for the 20 boxes of G_affine_reference.txt (commit 95d0843; the five integers c a1 a2 a3 e of the
#   affine form of G at scale 2^-64), at three points inside each box, is
#   |2^64 G - (c + a1 e1 + a2 e2 + a3 e3)| <= e, with e_i the coordinates of the point as G_affine_cert.py's
#   var() defines them, for G = (side A)/d and for G = (side B)/d ?
from mpmath import mp, mpf, sqrt, exp, sinh, sin, cos, asin, log, pi, quad, nstr

mp.dps = 50
NG = 40
H = mpf(1) / 32
THRESH = mpf(10) ** -10


def legendre(n, x):
    p0, p1 = mpf(1), x
    for k in range(2, n + 1):
        p0, p1 = p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k
    return p1, n * (x * p1 - p0) / (x * x - 1)


def gl_nodes(n):
    xs, ws = [], []
    for i in range(1, n + 1):
        x = cos(pi * (i - mpf(1) / 4) / (n + mpf(1) / 2))
        for _ in range(12):
            p, dp = legendre(n, x)
            x -= p / dp
        p, dp = legendre(n, x)
        xs.append(x)
        ws.append(2 / ((1 - x * x) * dp * dp))
    return xs, ws


XS, WS = gl_nodes(NG)


def integ(F, a, b):
    # int_a^b F(x) dx with x = sin(t)
    ta, tb = asin(a), asin(b)
    hm, md = (tb - ta) / 2, (tb + ta) / 2
    tot = mpf(0)
    for x, w in zip(XS, WS):
        t = md + hm * x
        tot += w * F(sin(t)) * cos(t)
    return hm * tot


def nu(x, r):
    w = sqrt(1 - x * x)
    z = r * w
    return w if z == 0 else w * sinh(z) / z


# ---------------- SIDE A: W from its definition ----------------
def cross(D):
    a, b = mpf(-999) / 1000, mpf(999) / 1000
    assert D(a) < 0 < D(b)
    for _ in range(10):
        m = (a + b) / 2
        if D(m) < 0:
            a = m
        else:
            b = m
    x0, x1 = a, b
    f0, f1 = D(x0), D(x1)
    for _ in range(80):
        if f1 == f0:
            break
        x0, f0, x1 = x1, f1, x1 - f1 * (x1 - x0) / (f1 - f0)
        f1 = D(x1)
        if abs(x1 - x0) < mpf(10) ** -46:
            break
    e = mpf(10) ** -40
    assert D(x1 - e) < 0 < D(x1 + e)
    return x1


def W(mu, r, d):
    s1, s2 = mu - d, mu + d
    Z1 = integ(lambda x: exp(s1 * x) * nu(x, r), -1, 1)
    Z2 = integ(lambda x: exp(s2 * x) * nu(x, r), -1, 1)

    def D(x):
        return (exp(s2 * x) / Z2 - exp(s1 * x) / Z1) * nu(x, r)
    xc = cross(D)
    absD = lambda x: abs(D(x))
    return (integ(absD, -1, xc) + integ(absD, xc, 1)) / 2, xc, D


def d2W(mu, r, d):
    f, xc = {}, None
    for k in (-8, -4, -2, -1, 0, 1, 2, 4, 8):
        f[k], x, _ = W(mu + k * H / 4, r, d)
        if k == 0:
            xc = x

    def S(j):
        h = j * H / 4
        return (-f[-2 * j] + 16 * f[-j] - 30 * f[0] + 16 * f[j] - f[2 * j]) / (12 * h * h)
    r1, r2 = (16 * S(2) - S(4)) / 15, (16 * S(1) - S(2)) / 15
    return (64 * r2 - r1) / 63, abs(r2 - r1) / 63, xc


# ---------------- SIDE B: the header's expression ----------------
def header_star(mu, r, d):
    s1, s2 = mu - d, mu + d

    def M(n, s):
        return integ(lambda x: x ** n * exp(s * x) * nu(x, r), -1, 1)
    Z1, Z2 = M(0, s1), M(0, s2)
    c = log(Z2 / Z1) / (2 * d)

    def N(n, s):
        return integ(lambda x: x ** n * exp(s * x) * nu(x, r), c, 1)

    def U(s, Z):
        m = M(1, s) / Z
        var = M(2, s) / Z - m * m
        return (N(2, s) - 2 * m * N(1, s) + m * m * N(0, s)) / Z - (N(0, s) / Z) * var, m
    U1, m1 = U(s1, Z1)
    U2, m2 = U(s2, Z2)
    q = exp(s2 * c) * nu(c, r) / Z2
    return U2 - U1 + q * (m2 - m1) ** 2 / (2 * d), c


# ---------------- sample points ----------------
def dec(s):
    return [mpf(t) for t in s.split()]


PTS = [(m, r, d) for d in dec("0.005 0.02 0.05 0.1 0.15 0.2") for r in dec("0 0.2 0.4 0.6 0.8")
       for m in dec("0 0.1 0.25 0.4 0.55 0.7 0.8")]
NREQ = len(PTS)
PTS += [(m, r, d) for d in dec("0.3 0.4") for r in dec("0 0.2 0.4 0.6 0.8") for m in dec("0 0.4 0.8")]

# G_affine_reference.txt: box edges in thousandths (mu_lo mu_hi r_lo r_hi d_lo d_hi), then c a1 a2 a3 e
REF = """0 100 0 100 0 100 -1266790716429935892 3557134024578336 748344278582536 1526502251810112 82338656494932946
0 100 300 400 100 200 -1242212458177538938 3378887674174930 4227659899120112 4095014398673686 108296932535555600
0 100 700 800 0 100 -1183221589807648788 3044526205946168 6986914419312056 1195713205100516 124950148888008854
100 200 200 300 100 200 -1237401795612110256 10044030711187738 3070227928645570 4109154848137548 125052044523504318
100 200 600 700 0 100 -1190236148441334592 9184538470511698 6370974524821538 1251589684336134 145526957628805340
200 300 100 200 100 200 -1215433405017197594 16578593652410168 1826712371173196 4003133054053806 142898345667154460
200 300 500 600 0 100 -1180933474200072130 15444430531608012 5522600828397162 1268633748413130 167684117532522460
300 400 0 100 100 200 -1176985554415256050 22729729694297458 589019528802966 3783972448050136 161692283914769966
300 400 400 500 0 100 -1155135094144978674 21587830703721030 4509738309136978 1245969481986758 191266853588888400
300 400 700 800 100 200 -1103517250960556140 19421819803269838 5746396846125966 3126844036817144 255584056854648562
400 500 300 400 0 100 -1113400333826130934 27378967584619594 3411301283726060 1185414705828862 216085322637195270
400 500 600 700 100 200 -1072157431500507356 25010513562747512 5044893822148008 3009210231405676 291576348556151582
500 600 200 300 0 100 -1057003935181788200 32601414361246104 2308913248194662 1091319994792838 241918882099207716
500 600 500 600 100 200 -1026028086781821450 30270641482310892 4212311122902392 2803816722568130 329554268393791048
600 700 100 200 0 100 -987852054605135500 37074968032372432 1278455279400610 970113744643224 268530021934989406
600 700 400 500 100 200 -966404637340869758 35011554512608860 3315005977505096 2522843290587362 369176916011120258
700 800 0 100 0 100 -908345956596571344 40668504431858664 382692217823358 829623752152320 295665608912325866
700 800 300 400 100 200 -895143819342847046 39073083718663634 2418381611102174 2183249915037464 410060407291678304
700 800 700 800 0 100 -861949143304862170 35893378613227812 4452266856645738 919738669572052 471483941525817214
400 405 400 410 126 154 -1131454374408286180 1291460300591990 524007866667978 982203762417704 3258472002879632"""
FRAC = [(4, 4, 4), (1, 7, 2), (7, 2, 7)]     # eighths of the box side, (mu, r, d)
SC = 1 << 64

if __name__ == "__main__":
    worst, wpt, werr, wc, neg, gmin, gmax = mpf(0), None, mpf(0), mpf(0), 0, None, None
    for (m, r, d) in PTS:
        A, err, xc = d2W(m, r, d)
        B, c = header_star(m, r, d)
        rel = abs(A - B) / abs(B)
        if rel > worst:
            worst, wpt = rel, (m, r, d)
        werr = max(werr, err / abs(B))
        wc = max(wc, abs(xc - c))
        neg += B < 0
        g = B / d
        gmin = g if gmin is None else min(gmin, g)
        gmax = g if gmax is None else max(gmax, g)
    print("sample points:", len(PTS), "(", NREQ, "on the grid d in 0.005..0.2, mu and r in 0..0.8;",
          len(PTS) - NREQ, "more at d = 0.3, 0.4 )")
    print("threshold fixed before the run: max |A - B|/|B| < 1e-10")
    print("max |A - B|/|B| =", nstr(worst, 2), "at (mu, r, d) = (" + ", ".join(nstr(v, 3) for v in wpt) + ")")
    print("below threshold:", bool(worst < THRESH))
    print("max size of the last Richardson correction, |r2 - r1|/63, over |B| =", nstr(werr, 2))
    print("max |root of q_s2 - q_s1  minus  header c| < 1e-35:", bool(wc < mpf(10) ** -35))
    print("header (*) < 0 at", int(neg), "of", len(PTS), "points; (*)/d in [", nstr(gmin, 6), ",", nstr(gmax, 6), "]")
    # quadrature check: W by this file's rule against mpmath's tanh-sinh quad in x, at four points
    qd = mpf(0)
    for (m, r, d) in (PTS[0], PTS[34], PTS[NREQ - 1], PTS[-1]):
        w, xc, D = W(m, r, d)
        qd = max(qd, abs(w - quad(lambda x: abs(D(x)), [-1, xc, 1]) / 2) / w)
    print("W: Gauss-Legendre in t against tanh-sinh in x, relative difference < 1e-30 at 4 points:",
          bool(qd < mpf(10) ** -30))
    # the 20 reference boxes
    okA = okB = n = 0
    ratio = ratb = mpf(0)
    for line in REF.splitlines():
        v = [int(t) for t in line.split()]
        pt = ((v[0], v[1]), (v[2], v[3]), (v[4], v[5]))
        for fr in FRAC:
            xyz, es = [], []
            for (lo, hi), f8 in zip(pt, fr):
                val = mpf(lo * (8 - f8) + hi * f8) / 8000
                cm = ((lo + hi) * SC) // 2000
                a = -((-(hi - lo) * SC) // 2000) + 1
                xyz.append(val)
                es.append((val * SC - cm) / a)
            lin = v[6] + v[7] * es[0] + v[8] * es[1] + v[9] * es[2]
            A, err, xc = d2W(*xyz)
            B, c = header_star(*xyz)
            ra, rb = abs(SC * A / xyz[2] - lin) / v[10], abs(SC * B / xyz[2] - lin) / v[10]
            okA += ra <= 1
            okB += rb <= 1
            ratio, ratb = max(ratio, ra), max(ratb, rb)
            n += 1
    print("reference boxes: 20; points:", n, "; side A inside the affine enclosure:", int(okA),
          "; side B inside:", int(okB))
    print("max |2^64 G - affine part|/e: side A", nstr(ratio, 3), "; side B", nstr(ratb, 3))
