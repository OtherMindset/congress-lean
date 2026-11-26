"""vEHL sanity checks.
(1) phi_beta({o}) = 4 <phi^2>_{single site} for a = 2 + eps^2 mu_b/2, b = lam eps^2  (inf_S phi_beta(S) <= this).
(2) exact enumeration on a 3-site path, discrete symmetric spins: verify
    <phi_o; phi_z^2> = 4 E[xi-_o xi-_z xi+_z 1(o<-> z in w-) 1(z <-> g in w+)]   (site identity)
    <phi_o; phi_u phi_v> = 2 E[xi-_o xi-_u xi+_v 1(o<->u in w-) 1(v<->g in w+)] + (u<->v)  (bond identity, vEHL)
    and the decoupling direction E[fg] <= E f E g (Prop 6 => GHS u3(o,z,z)<=0).
"""
import itertools, math, sys
import mpmath as mp
mp.mp.dps = 30

def onesite_phi(eps, lam, mu):
    ceps = mp.log(1/eps)/(2*mp.pi)
    mub = mu - 12*lam*ceps
    a = 2 + eps**2*mub/2; b = lam*eps**2
    f = lambda x: mp.exp(-a*x**2 - b*x**4)
    Z = mp.quad(f, [-mp.inf, 0, mp.inf]); s2 = mp.quad(lambda x: x**2*f(x), [-mp.inf, 0, mp.inf])/Z
    return a, 4*s2

print("(1) phi_1({o}) = 4<phi^2>_1site, lam=1, mu=0")
for n in range(2, 11):
    eps = mp.mpf(2)**-n
    a, p = onesite_phi(eps, 1, 0)
    print(f"  eps=2^-{n}: a={float(a):.8f}  phi({{o}})-1 = {float(p-1):+.3e}   (phi-1)/(eps^2 log(1/eps)) = {float((p-1)/(eps**2*mp.log(1/eps))):+.4f}")

# (2) enumeration
def run(vals, wts, beta, H, a):
    n = 3; edges = [(0,1),(1,2)]
    sw = {v: w*math.exp(-a*v*v) for v, w in zip(vals, wts)}
    def conn_cc(n, open_edges, ghost_open=None):
        par = list(range(n+1))
        def f(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        for (u, v) in open_edges: par[f(u)] = f(v)
        if ghost_open:
            for u in ghost_open: par[f(u)] = f(n)
        return f
    Z = 0; mom = {}
    acc_site = [0.0]*n; acc_bond = {e: 0.0 for e in edges}; accf = [0.0]*n; accg = [0.0]*n
    # direct correlations
    Zs = 0; S1 = [0]*n; S2 = [0]*n; S12 = [[0]*n for _ in range(n)]; S1p = [[0]*n for _ in range(n)]
    for phi in itertools.product(vals, repeat=n):
        w = math.exp(beta*sum(phi[u]*phi[v] for u, v in edges) + H*sum(phi))
        for x in phi: w *= sw[x]
        Zs += w
        for i in range(n):
            S1[i] += w*phi[i]; S2[i] += w*phi[i]**2
            for j in range(n):
                S12[i][j] += w*phi[i]*phi[j]**2; S1p[i][j] += w*phi[i]*phi[j]
    m = [s/Zs for s in S1]; q = [s/Zs for s in S2]
    site_direct = [S12[0][z]/Zs - m[0]*q[z] for z in range(n)]
    bond_direct = {(u, v): (S1p[u][v]*0) for (u, v) in edges}
    # <phi_o; phi_u phi_v>
    for (u, v) in edges:
        s = 0
        for phi in itertools.product(vals, repeat=n):
            w = math.exp(beta*sum(phi[x]*phi[y] for x, y in edges) + H*sum(phi))
            for x in phi: w *= sw[x]
            s += w*phi[0]*phi[u]*phi[v]
        bond_direct[(u, v)] = s/Zs - m[0]*(S1p[u][v]/Zs)
    # representation
    for phi in itertools.product(vals, repeat=n):
        wa = math.exp(beta*sum(phi[u]*phi[v] for u, v in edges) + H*sum(phi))
        for x in phi: wa *= sw[x]
        for phip in itertools.product(vals, repeat=n):
            wb = math.exp(beta*sum(phip[u]*phip[v] for u, v in edges) + H*sum(phip))
            for x in phip: wb *= sw[x]
            W = wa*wb/Zs**2
            pp = [(phi[i]+phip[i])/2 for i in range(n)]; pm = [(phi[i]-phip[i])/2 for i in range(n)]
            xp = [abs(t) for t in pp]; xm = [abs(t) for t in pm]
            # w+ : edges + ghost edges
            cand_p = [(e, 1-math.exp(-4*beta*xp[e[0]]*xp[e[1]])) if pp[e[0]]*pp[e[1]] > 0 else (e, 0.0) for e in edges]
            cand_g = [(u, 1-math.exp(-4*H*xp[u])) if pp[u] > 0 else (u, 0.0) for u in range(n)]
            cand_m = [(e, 1-math.exp(-4*beta*xm[e[0]]*xm[e[1]])) if pm[e[0]]*pm[e[1]] > 0 else (e, 0.0) for e in edges]
            for op in itertools.product([0, 1], repeat=len(edges)+n):
                pr = 1.0; oe = []; og = []
                for k, (e, p) in enumerate(cand_p):
                    pr *= p if op[k] else 1-p
                    if op[k]: oe.append(e)
                for k, (u, p) in enumerate(cand_g):
                    pr *= p if op[len(edges)+k] else 1-p
                    if op[len(edges)+k]: og.append(u)
                if pr == 0: continue
                fp = conn_cc(n, oe, og)
                for om in itertools.product([0, 1], repeat=len(edges)):
                    pr2 = pr; me = []
                    for k, (e, p) in enumerate(cand_m):
                        pr2 *= p if om[k] else 1-p
                        if om[k]: me.append(e)
                    if pr2 == 0: continue
                    fm = conn_cc(n, me)
                    WW = W*pr2
                    for z in range(n):
                        A = xm[0]*xm[z]*(fm(0) == fm(z)); B = xp[z]*(fp(z) == fp(n))
                        acc_site[z] += WW*A*B; accf[z] += WW*A; accg[z] += WW*B
                    for (u, v) in edges:
                        t = xm[0]*xm[u]*xp[v]*(fm(0) == fm(u))*(fp(v) == fp(n)) + xm[0]*xm[v]*xp[u]*(fm(0) == fm(v))*(fp(u) == fp(n))
                        acc_bond[(u, v)] += WW*t
    return m, site_direct, [4*x for x in acc_site], bond_direct, {e: 2*acc_bond[e] for e in edges}, [4*accf[z]*accg[z] for z in range(n)]

for (vals, wts, beta, H, a) in [((-2,-1,1,2), (1,1,1,1), 0.3, 0.2, 0.25), ((-1.5,-0.5,0.5,1.5), (1,1,1,1), 0.8, 0.05, 0.1)]:
    m, sd, sr, bd, br, dec = run(vals, wts, beta, H, a)
    print(f"\n(2) vals={vals} beta={beta} H={H} a={a}: m_o={m[0]:.6f}")
    for z in range(3):
        print(f"   site z={z}: direct <phi_o;phi_z^2>={sd[z]:.10f}  rep={sr[z]:.10f}  decoupled 4E[f]E[g]={dec[z]:.6f}  (rep<=dec: {sr[z]<=dec[z]+1e-12})")
    for e in bd:
        print(f"   bond {e}: direct <phi_o;phi_u phi_v>={bd[e]:.10f}  rep={br[e]:.10f}")
