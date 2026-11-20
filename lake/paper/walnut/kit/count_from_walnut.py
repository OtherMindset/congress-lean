"""From Walnut's Sage output for V<R>_S, _X, _Y, _O (linear representations in g, lsd_2), compute
c_R(n) = 4S - 2X - 2Y + O at g = 2^n - 1 and prove D*c(n) = a*4^n + b*2^n + c for n >= n0:
the difference has a linear representation of dimension m = sum of the four sizes + 3, so it is zero
for all n >= n0 once it is zero on m consecutive values from n0 (Cayley-Hamilton). Exact integers.
Usage: python3 count_from_walnut.py <Result dir>"""
import re, sys, os, json, time
RES = sys.argv[1]
CASES = {'V926': (0, 3, 4, 0, -1), 'V654': (3, 48, 53, 0, -80)}   # n0, D, a, b, c
def parse(path):
    txt = open(path).read()
    def mat(name):
        m = re.search(name + r' = matrix\(ZZ, (\d+), (\d+), \[(.*?)\]\)\n', txt, re.S)
        r, c, body = int(m.group(1)), int(m.group(2)), m.group(3)
        nums = [int(x) for x in re.findall(r'-?\d+', body)]
        assert len(nums) == r * c, (name, len(nums), r, c)
        return [nums[i * c:(i + 1) * c] for i in range(r)]
    v = mat('v')[0]; w = [row[0] for row in mat('w')]
    M = {d: mat(f'M_g_{d}') for d in (0, 1)}
    sp = {d: [[(j, x) for j, x in enumerate(row) if x] for row in M[d]] for d in M}
    return v, w, sp
def vecmul(u, sp):
    out = [0] * len(sp)
    for i, ui in enumerate(u):
        if ui:
            for j, x in sp[i]: out[j] += ui * x
    return out
def seq(rep, N, pad=0):
    v, w, sp = rep; u = v[:]; vals = []
    for n in range(N + 1):
        z = u[:]
        for _ in range(pad): z = vecmul(z, sp[0])
        vals.append(sum(a * b for a, b in zip(z, w)))
        u = vecmul(u, sp[1])
    return vals
report = {}
for name, (n0, D, a, b, c) in CASES.items():
    t0 = time.time()
    reps = {k: parse(os.path.join(RES, f'{name}_{k}.sage')) for k in 'SXYO'}
    sizes = {k: len(reps[k][0]) for k in reps}
    m = sum(sizes.values()) + 3
    N = n0 + m + 2
    S = {k: seq(reps[k], N) for k in reps}
    pad_ok = all(seq(reps[k], 12, pad=p) == S[k][:13] for k in reps for p in (1, 2))
    cnt = [4 * S['S'][n] - 2 * S['X'][n] - 2 * S['Y'][n] + S['O'][n] for n in range(N + 1)]
    ok = all(D * cnt[n] == a * 4 ** n + b * 2 ** n + c for n in range(n0, N + 1))
    report[name] = dict(sizes=sizes, dimension=m, checked_n=f'{n0}..{N}', padding_stable=pad_ok,
                        formula_holds=ok, first_terms=cnt[:10], seconds=round(time.time() - t0, 1))
    print(name, json.dumps(report[name]))
sim = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sim_n9.json')))
for name in report:
    R = name[1:]
    if R in sim: print(name, 'matches direct simulation n<=9:', sim[R][:10] == report[name]['first_terms'][:len(sim[R][:10])], sim[R][:10])
