#!/usr/bin/env python3
"""Build vn_negative.txt (Walnut negative controls) and two mutated automata, and check every expected answer
in Python first, by evaluating the automata on a window. Usage:
  python3 -I make_negative.py <kit dir> <out dir>
Writes <out>/Command Files/vn_negative.txt, <out>/Automata Library/V926m.txt, V654m.txt and <out>/expected.txt."""
import os, sys, itertools
kit, out = sys.argv[1:3]
LIB = os.path.join(kit, 'Automata Library')

def load(path):
    lines = [l.strip() for l in open(path) if l.strip()]
    assert lines[0] == 'lsd_2 lsd_2 lsd_2'
    out_, delta, cur = {}, {}, None
    for l in lines[1:]:
        if '->' in l:
            a, b = l.split('->'); x, y, t = map(int, a.split()); delta[(cur, x, y, t)] = int(b)
        else:
            s, o = map(int, l.split()); cur = s; out_[s] = o
    return out_, delta

def text(aut):
    out_, delta = aut; res = ['lsd_2 lsd_2 lsd_2', '']
    for s in sorted(out_):
        res.append(f'{s} {out_[s]}')
        res += [f'{x} {y} {t} -> {delta[(s, x, y, t)]}' for (q, x, y, t) in sorted(delta, key=lambda k: (k[0], k[3], k[2], k[1])) if q == s]
        res.append('')
    return '\n'.join(res)

def V(aut, x, y, t):
    out_, delta = aut; s = 0
    while x or y or t:
        s = delta.get((s, x & 1, y & 1, t & 1))
        if s is None: return 0     # missing transition: Walnut treats it as rejection
        x >>= 1; y >>= 1; t >>= 1
    return out_[s]

def rule_ok(aut, R, W=64, T=64):
    """True iff V(.,.,c+1) is rule R applied to V(.,.,c) (mirror at 0) on x, y < W, 1 <= c < T."""
    for c in range(1, T):
        for x in range(W):
            for y in range(W):
                n = [V(aut, x + 1, y, c), V(aut, x, y + 1, c), V(aut, abs(x - 1), y, c), V(aut, x, abs(y - 1), c)]
                if V(aut, x, y, c + 1) != (R >> (V(aut, x, y, c) + 2 * sum(n))) & 1: return False
    return True

def seed_ok(aut, at=(0, 0), W=64):
    return all(V(aut, x, y, 1) == ((x, y) == at) for x in range(W) for y in range(W))

def formula(name, R):
    c = f'${name}(a,b,c)'
    nb = [f'${name}(a+1,b,c)', f'${name}(a,b+1,c)',
          f'((a=0 & ${name}(1,b,c)) | (Eu (u+1=a & ${name}(u,b,c))))',
          f'((b=0 & ${name}(a,1,c)) | (Ev (v+1=b & ${name}(a,v,c))))']
    terms = []
    for ctr in (0, 1):
        for on in itertools.product((0, 1), repeat=4):
            if (R >> (ctr + 2 * sum(on))) & 1:
                lits = [c if ctr else '~' + c] + [p if o else '~' + p for p, o in zip(nb, on)]
                terms.append('(' + ' & '.join(lits) + ')')
    body = ' | '.join(terms) if terms else 'false'
    return f'?lsd_2 Aa,b,c (c>=1) => (${name}(a,b,c+1) <=> ({body}))'

def Vpad(aut, x, y, t, pad):
    out_, delta = aut; s = 0; k = max(x, y, t).bit_length() + pad
    for _ in range(k):
        s = delta.get((s, x & 1, y & 1, t & 1))
        if s is None: return 0
        x >>= 1; y >>= 1; t >>= 1
    return out_[s]

def pad_ok(aut, W=32, T=32):
    """Walnut reads lsd_2 inputs padded with zeros: the value must not depend on the padding."""
    return all(Vpad(aut, x, y, t, p) == V(aut, x, y, t) for p in (1, 2, 3) for x in range(W) for y in range(W)
               for t in range(T + 2))

def mutate(aut):
    """Candidates: one transition on a nonzero digit triple changed to another state."""
    out_, delta = aut
    for key in sorted(delta):
        if key[1:] == (0, 0, 0): continue
        for new in sorted(out_):
            if new != delta[key]:
                d2 = dict(delta); d2[key] = new
                yield key, delta[key], new, (out_, d2)

A = {n: load(os.path.join(LIB, f'{n}.txt')) for n in ('V926', 'V654')}
assert rule_ok(A['V926'], 926) and rule_ok(A['V654'], 654) and rule_ok(A['V926'], 990)
assert seed_ok(A['V926']) and seed_ok(A['V654']) and pad_ok(A['V926']) and pad_ok(A['V654'])
mut = {}
for n, R in (('V926', 926), ('V654', 654)):
    for key, old, new, m in mutate(A[n]):
        if seed_ok(m) and pad_ok(m) and not rule_ok(m, R, 32, 32):
            mut[n] = (key, old, new, m); break
cmds, exp = [], []
def add(label, sentence, expect, why):
    cmds.append(f'eval {label} "{sentence}";'); exp.append(f'{label}: expected {expect} ({why})')
for n, R in (('V926', 926), ('V654', 654)):
    key, old, new, m = mut[n]
    open_dir = os.path.join(out, 'Automata Library'); os.makedirs(open_dir, exist_ok=True)
    open(os.path.join(open_dir, n + 'm.txt'), 'w').write(text(m) + '\n')
    add(n + 'm_step', formula(n + 'm', R), 'FALSE', f'{n} with transition state {key[0]} on (x,y,t) digits {key[1:]} changed from {old} to {new}')
    add(n + 'm_seed', f'?lsd_2 Aa,b (${n}m(a,b,1) <=> (a=0 & b=0))', 'TRUE', 'the change leaves every value at t = 1 unchanged')
for n, R, why in (('V926', 654, 'Rule 926 table under Rule 654'), ('V654', 926, 'Rule 654 table under Rule 926'),
                  ('V926', 598, 'Rule 926 table under Rule 598')):
    assert not rule_ok(A[n], R, 32, 32)
    add(f'{n}_under{R}', formula(n, R), 'FALSE', why)
add('V926_seed10', '?lsd_2 Aa,b ($V926(a,b,1) <=> (a=1 & b=0))', 'FALSE', 'seed moved to (1,0)')
assert any(not V(A['V926'], x, y, c) and V(A['V926'], x, y, c + 1) for x in range(32) for y in range(32) for c in range(1, 32))
add('V926_grows', '?lsd_2 Ea,b,c (c>=1 & ~$V926(a,b,c) & $V926(a,b,c+1))', 'TRUE', 'some cell turns ON after stage 1')
add('V926_step_regen', formula('V926', 926), 'TRUE', 'formula regenerated by this script: must agree with vn_compare.txt')
cdir = os.path.join(out, 'Command Files'); os.makedirs(cdir, exist_ok=True)
open(os.path.join(cdir, 'vn_negative.txt'), 'w').write('\n'.join(cmds) + '\nquit;\n')
open(os.path.join(out, 'expected.txt'), 'w').write('\n'.join(exp) + '\n')
print('\n'.join(exp))
