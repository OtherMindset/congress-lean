"""One-site check of (C.1)-(C.2): zeros of Z(h)=E e^{h phi} (phi ~ e^{-a phi^2 - b phi^4}) at h = i alpha_j,
i.e. real zeros of F(alpha) = E cos(alpha phi). Check sum alpha^-2 = kappa2/2, sum alpha^-4 = -kappa4/12,
B = -3 sum w_j^2, and 3 w1^2 <= |B| <= 3 w1. Taylor series of F with exact moments at high precision."""
import mpmath as mp
mp.mp.dps = 400

def moments(a, b, K):
    a = mp.mpf(a); b = mp.mpf(b)
    def M(j):  # int_0^inf phi^{2j} e^{-a phi^2 - b phi^4}
        f = lambda p: p ** (2 * j) * mp.exp(-a * p * p - b * p ** 4)
        return mp.quad(f, [0, 1, 2, 4, 8, mp.inf])
    Ms = [M(0), M(1)]
    for k in range(0, 2 * K):  # (2k+1) M_k = 2a M_{k+1} + 4b M_{k+2}   (M_k := int phi^{2k})
        Ms.append(((2 * k + 1) * Ms[k] - 2 * a * Ms[k + 1]) / (4 * b))
    return Ms, M

def run(a, b, nz=40, K=700):
    Ms, Mq = moments(a, b, K)
    # sanity: recurrence vs quadrature at a high moment
    jj = 40
    rel = abs(Ms[jj] / Mq(jj) - 1)
    c = [(-1) ** k * Ms[k] / Ms[0] / mp.factorial(2 * k) for k in range(len(Ms))]
    def F(al):
        s = mp.mpf(0); x2 = al * al; p = mp.mpf(1)
        for k in range(len(c)):
            term = c[k] * p
            s += term
            if k > 10 and abs(term) < mp.mpf(10) ** (-60) * (1 + abs(s)):
                break
            p *= x2
        return s
    m2 = Ms[1] / Ms[0]; m4 = Ms[2] / Ms[0]
    k2 = m2; k4 = m4 - 3 * m2 ** 2; B = k4 / k2 ** 2
    # scan for sign changes
    zeros = []; al = mp.mpf('0.01'); f0 = F(al); step = mp.mpf('0.02')
    while len(zeros) < nz:
        al2 = al + step; f1 = F(al2)
        if mp.sign(f1) != mp.sign(f0):
            zeros.append(mp.findroot(F, (al, al2), solver='anderson'))
        al, f0 = al2, f1
        if al > 200: break
    s2 = sum(z ** -2 for z in zeros); s4 = sum(z ** -4 for z in zeros)
    # tail fit alpha_k ~ C (k - k0)^{3/4} from last 3 zeros
    n = len(zeros)
    z1, z2 = zeros[-2], zeros[-1]
    # solve (z2/z1)^{4/3} = (n - k0)/(n-1-k0)
    r = (z2 / z1) ** (mp.mpf(4) / 3)
    k0 = (n - r * (n - 1)) / (1 - r)
    C = z2 / (n - k0) ** mp.mpf(0.75)
    tail2 = 2 / C ** 2 * (n + mp.mpf(0.5) - k0) ** mp.mpf(-0.5)
    tail4 = mp.mpf(2) / 5 * C ** -4 * (n + mp.mpf(0.5) - k0) ** mp.mpf(-2.5) * mp.mpf(5) / 4  # int k^{-3} = 1/(2k^2)
    tail4 = C ** -4 * (n + mp.mpf(0.5) - k0) ** -2 / 2
    S2 = s2 + tail2; S4 = s4 + tail4
    w = [z ** -2 / S2 for z in zeros]
    Bly = -3 * (S4 / S2 ** 2)
    w1 = w[0]
    print(f"a={a} b={b}: first zeros {[float(mp.nstr(z,8)) for z in zeros[:4]]} ... alpha_{n}={float(zeros[-1]):.4f}; recurrence check rel={float(rel):.1e}")
    print(f"   kappa2/2={float(k2/2):.10f}  sum alpha^-2 ({n} zeros)={float(s2):.10f} +tail {float(tail2):.2e} = {float(S2):.10f}  rel={float(abs(S2/(k2/2)-1)):.1e}")
    print(f"   -kappa4/12={float(-k4/12):.10f}  sum alpha^-4={float(s4):.10f} +tail {float(tail4):.1e}  rel={float(abs(S4/(-k4/12)-1)):.1e}")
    print(f"   |B| direct={float(-B):.8f}  3 sum w^2={float(-Bly):.8f}  3w1^2={float(3*w1**2):.6f} <= |B| <= 3w1={float(3*w1):.6f} : {bool(3*w1**2 <= -B <= 3*w1)}; alpha1^2 kappa2={float(zeros[0]**2*k2):.5f}")

if __name__ == '__main__':
    for a, b in [(1, 0.5), (0, 1), (-2, 0.3), (-6, 1), (2, 0.05)]:
        run(a, b)
