#!/usr/bin/env python3
"""Negative controls for the Walnut count route: the post-processing of count_from_walnut.py, run with changed
closed forms. Each must report formula_holds = false. Usage: python3 -I count_negative.py <kit dir> <Result dir>"""
import sys, os
kit, res = sys.argv[1:3]
src = open(os.path.join(kit, 'count_from_walnut.py')).read()
head = src.split('report = {}')[0]          # the parsing and evaluation functions only
ns = {'__file__': os.path.join(kit, 'count_from_walnut.py')}
sys_argv = sys.argv; sys.argv = ['x', res]
exec(compile(head, 'count_from_walnut.py', 'exec'), ns)
sys.argv = sys_argv
CONTROLS = [('V926', (0, 3, 4, 0, -1), 'correct (control of the control)'),
            ('V926', (0, 3, 4, 0, 1), 'constant -1 -> +1'),
            ('V926', (0, 3, 4, 1, -1), 'coefficient of 2^n 0 -> 1'),
            ('V926', (1, 3, 5, 0, -1), 'leading coefficient 4 -> 5'),
            ('V654', (3, 48, 53, 0, -80), 'correct (control of the control)'),
            ('V654', (3, 48, 53, 0, -79), 'constant -80 -> -79'),
            ('V654', (2, 48, 53, 0, -80), 'starting index 3 -> 2'),
            ('V654', (3, 47, 53, 0, -80), 'denominator 48 -> 47')]
for name, (n0, D, a, b, c), what in CONTROLS:
    reps = {k: ns['parse'](os.path.join(res, f'{name}_{k}.sage')) for k in 'SXYO'}
    m = sum(len(reps[k][0]) for k in reps) + 3
    N = n0 + m + 2
    S = {k: ns['seq'](reps[k], N) for k in reps}
    cnt = [4 * S['S'][n] - 2 * S['X'][n] - 2 * S['Y'][n] + S['O'][n] for n in range(N + 1)]
    bad = [n for n in range(n0, N + 1) if D * cnt[n] != a * 4 ** n + b * 2 ** n + c]
    print(f'{name}  {D}c(n) = {a}*4^n + {b}*2^n + {c}, n >= {n0}  [{what}]:',
          'formula_holds = true' if not bad else f'formula_holds = false (first failure at n = {bad[0]})')
