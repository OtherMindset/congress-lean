"""B = V case (homogeneous field, whole-graph magnetisation): R = F'''/F' + 2F'' with F = log Z(H).
Target: k1 k4 - k2 k3 + 2 k1^2 k3 <= 0 (k_n = F^(n)). Test for Lee-Yang-type F:
 (a) F = sum_k log cosh(a_k H)            (independent weighted Ising spins; positive measure)
 (b) F = b H^2 + sum_k log(1 + H^2/al_k^2)  (general LY product; positivity not enforced)
 (c) single factor log(1+H^2) and log cosh separately."""
import sympy as sp, numpy as np
H = sp.symbols('H', positive=True)
def expr(F):
    k = [sp.diff(F, H, n) for n in range(5)]
    return sp.simplify(k[1]*k[4] - k[2]*k[3] + 2*k[1]**2*k[3])
a = sp.symbols('a', positive=True)
print("single log cosh(aH):", sp.simplify(expr(sp.log(sp.cosh(a*H)))))
print("single log(1+H^2):", sp.factor(expr(sp.log(1 + H**2))))
print("Gaussian bH^2:", expr(sp.Symbol('b', positive=True)*H**2))
rng = np.random.default_rng(0)
def num(Ff, Hs):
    out = []
    for h in Hs:
        k = [Ff(h, n) for n in range(5)]
        v = k[1]*k[4] - k[2]*k[3] + 2*k[1]**2*k[3]; s = abs(k[1]*k[4]) + abs(k[2]*k[3]) + abs(2*k[1]**2*k[3])
        out.append(v/s)
    return max(out)
# derivatives of log cosh(aH): t = tanh(aH)
def lc(h, n, a):
    t = np.tanh(a*h)
    return [np.log(np.cosh(a*h)), a*t, a**2*(1-t**2), -2*a**3*t*(1-t**2), a**4*(1-t**2)*(6*t**2-2)][n]
def lp(h, n, al):  # log(1+h^2/al^2)
    x = h/al
    d = [np.log(1+x*x), 2*x/(1+x*x), 2*(1-x*x)/(1+x*x)**2, 4*x*(x*x-3)/(1+x*x)**3, -12*(x**4-6*x*x+1)/(1+x*x)**4]
    return d[n]/al**n
Hs = np.logspace(-3, 1.5, 400)
w = -1
for t in range(2000):
    A = 10**rng.uniform(-1.5, 1.5, rng.integers(1, 6))
    w = max(w, num(lambda h, n: sum(lc(h, n, a) for a in A), Hs))
print("(a) sum log cosh worst rel:", w)
w = -1; arg = None
for t in range(2000):
    AL = 10**rng.uniform(-1, 1, rng.integers(1, 6)); b = 10**rng.uniform(-2, 1)*(rng.random() < .5)
    g = lambda h, n: sum(lp(h, n, al) for al in AL) + [b*h*h, 2*b*h, 2*b, 0, 0][n]
    r = num(g, Hs)
    if r > w: w, arg = r, (AL, b)
print("(b) general LY product worst rel:", w, arg)
