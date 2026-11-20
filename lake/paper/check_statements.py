#!/usr/bin/env python3
"""Mechanical statement check (paper, Section 9.2).

For every top-level theorem, compare the statement Lean elaborated (as the runner printed it, stored in the
artifact's manifest.json) with the claim the paper prints for it (rows.json, generated from the ledger, plus the
main-text theorems listed in MAIN below).

Usage: python3 -I check_statements.py rows.json manifest.json [report.txt]

Shapes (paper, Section 9.1):
  1 closed form      forall n, [n0 <= n ->] [D *] count(R, 2^n-1) = rhs(n)
  2 equal counts     forall n, [k <= n ->] count(S, 2^n-1) = count(R, 2^n-1)
  3 equal evolutions caState S = caState R
  4 the rest         relations of Table 3 and the main-text theorems

Closed forms are compared as functions of n: both sides are evaluated exactly, with Lean's truncated subtraction
in natural-number exponents, at the 41 values of n from the lower bound on. Beyond the truncation points each side
is a linear combination of powers b^n of a few fixed integers b, so agreement at more consecutive values than there
are distinct b implies agreement for every n. Hypotheses are compared exactly. Statements that no
template covers are printed in full for reading.
"""
import ast
import json
import re
import sys
from fractions import Fraction

NAT = r'∀ \(n : ℕ\), '
CNT = r'↑?\(?LT2D\.onCount (\d+) \(2 \^ n - 1\)\)?'


def lean_eval(expr, n):
    """Evaluate a Lean integer expression in n (ints, + - * ^, parentheses). Exponents are natural numbers:
    subtraction inside an exponent is truncated, as in Lean."""
    tree = ast.parse(expr.replace('^', '**'), mode='eval')

    def ev(node, nat):
        if isinstance(node, ast.Expression):
            return ev(node.body, nat)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.Name) and node.id == 'n':
            return n
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub) and not nat:
            return -ev(node.operand, nat)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                return ev(node.left, nat) ** ev(node.right, True)
            a, b = ev(node.left, nat), ev(node.right, nat)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.Sub):
                return max(a - b, 0) if nat else a - b
        raise ValueError('unsupported: ' + ast.dump(node))

    return ev(tree, False)


def latex_eval(tex, n):
    s = tex.replace('\\cdot', '*').replace('\\,', '').replace('\\bigl', '').replace('\\bigr', '')
    s = re.sub(r'\^\{([^}]*)\}', r'^(\1)', s)
    s = re.sub(r'\\tfrac\{([^}]*)\}\{([^}]*)\}', r'(\1)/(\2)', s)
    s = re.sub(r'\\frac\{([^}]*)\}\{([^}]*)\}', r'(\1)/(\2)', s)
    s = s.replace('{', '(').replace('}', ')')
    s = re.sub(r'(\d|\))\s*\(', r'\1*(', s)
    s = s.replace('^', '**')
    if re.search(r'[^0-9n+\-*/() ]', s):
        raise ValueError('latex not understood: ' + tex)
    # exact rational evaluation
    return eval(re.sub(r'(\d+)', r'Fraction(\1)', s), {'Fraction': Fraction, 'n': Fraction(n)})


def parse(stmt):
    """Return a dict describing the statement, or None if no template applies."""
    s = ' '.join(stmt.split())
    # a statement in m about stage 2^(m+k)-1 is the statement in n = m+k for n >= k
    m = re.fullmatch(r'∀ \(m : ℕ\), (.*)', s)
    if m and not re.search(r'\bn\b', m[1]) and (k := set(re.findall(r'\(2 \^ \(m \+ (\d+)\) - 1\)', m[1]))) and len(k) == 1:
        k = int(k.pop())
        body = re.sub(r'\(m \+ (\d+)\)', lambda j: 'n' if int(j[1]) == k else
                      f'(n + {int(j[1]) - k})' if int(j[1]) > k else j[0], m[1])
        if not re.search(r'\bm\b', body):
            st = parse('∀ (n : ℕ), ' + body)
            if st and st.get('hyp') == ('ge', 0):
                st['hyp'] = ('ge', k)
                st['via'] = f'n = m + {k}'
                return st
    m = re.fullmatch(r'∀ \(g : ℕ\), LT2D\.onCount (\d+) g = LT2D\.onCount (\d+) g', s)
    if m:
        return {'shape': 2, 'S': int(m[1]), 'R': int(m[2]), 'hyp': ('ge', 0), 'every_stage': True}
    m = re.fullmatch(r'LT2D\.caState (\d+) = LT2D\.caState (\d+)', s)
    if m:
        return {'shape': 3, 'S': int(m[1]), 'R': int(m[2])}
    m = re.fullmatch(NAT + r'(?:(\d+) ≤ n → |n ≠ (\d+) → )?(?:(\d+) \* )?' + CNT + r' = (.*)', s)
    if not m:
        return None
    lo, ne, d, r, rhs = m.groups()
    hyp = ('ge', int(lo)) if lo else ('ne', int(ne)) if ne else ('ge', 0)
    m2 = re.fullmatch(CNT + r'(?: ↔ n ≠ (\d+))?', rhs)
    if m2:
        if d:
            return None
        iff = m2[2]
        if iff:
            if hyp != ('ge', 0):
                return None
            return {'shape': 4, 'kind': 'iff', 'S': int(r), 'R': int(m2[1]), 'k': int(iff)}
        return {'shape': 2, 'S': int(r), 'R': int(m2[1]), 'hyp': hyp}
    if 'LT2D' in rhs:
        return None
    return {'shape': 1, 'R': int(r), 'D': int(d or 1), 'rhs': rhs, 'hyp': hyp}


def holds(hyp, n):
    return n >= hyp[1] if hyp[0] == 'ge' else n != hyp[1]


def same_function(stmt, expect, start):
    """Compare count(n) = rhs(n)/D (statement) with expect(n) on n = start .. start+40 where the hypothesis holds."""
    bad = []
    for n in range(start, start + 41):
        if not holds(stmt['hyp'], n):
            continue
        lhs = Fraction(lean_eval(stmt['rhs'], n), stmt['D'])
        if lhs != expect(n):
            bad.append((n, lhs, expect(n)))
    return bad


# Main-text theorems: the claim as the paper states it (Theorems 6, 8, 9 and Section 7.3).
MAIN = {
    'LT2D.a169707_rule750': ('closed', 750, 0, lambda n: Fraction(4 ** (n + 1) - 1, 3), 'Theorem 8'),
    'LT2D.r990_count': ('closed', 990, 0, lambda n: Fraction(4 ** (n + 1) - 1, 3), 'Section 6.2'),
    'LT2D.r990_caState_eq_926': ('evol', 990, 926, None, 'Section 6.2'),
}


def main():
    rows = json.load(open(sys.argv[1]))['rows']
    thms = {t['name']: t for t in json.load(open(sys.argv[2]))['top_level_theorems']}
    out = open(sys.argv[3], 'w') if len(sys.argv) > 3 else sys.stdout
    seen, results = set(), []

    def record(name, status, note):
        seen.add(name)
        results.append((name, status, note))

    for row in rows:
        if row['table'] == 'formulas':
            name = row['theorem']
            st = parse(thms[name]['runner_statement'])
            A, B, C, D = (Fraction(row[k]) for k in 'ABCD')
            tab = lambda n: (A * 4 ** n + B * 2 ** n + C) / (16 * D)
            notes = []
            if not st or st['shape'] != 1:
                record(name, 'UNTEMPLATED', 'Table 1 row ' + row['a_number'])
                continue
            if st['R'] != row['rule']:
                notes.append(f"rule {st['R']} != {row['rule']}")
            # the row's printed formula must equal its (A,B,C,D) data
            for n in range(row['n0'], row['n0'] + 41):
                if latex_eval(row['latex'], n) != tab(n):
                    notes.append(f"printed formula != row data at n={n}")
                    break
            bad = same_function(st, tab, min(row['n0'], st['hyp'][1] if st['hyp'][0] == 'ge' else 0))
            bad = [b for b in bad if b[0] >= row['n0']]
            if bad:
                notes.append(f"value differs at n={bad[0][0]}")
            if st['hyp'] == ('ge', row['n0']):
                hyp_note = ''
            elif st['hyp'][0] == 'ge' and st['hyp'][1] < row['n0']:
                hyp_note = f"statement holds from n={st['hyp'][1]}, table says n>={row['n0']} (stronger)"
            else:
                notes.append(f"hypothesis {st['hyp']} vs table n>={row['n0']}")
                hyp_note = ''
            record(name, 'MISMATCH' if notes else 'MATCH',
                   '; '.join(notes) or (f"Table 1 {row['a_number']}, Rule {row['rule']}" + (', ' + hyp_note if hyp_note else '')
                                          + (f", statement in m with {st['via']}" if st.get('via') else '')))
        elif row['table'] == 'equal':
            for other, name in zip(row['others'], row['theorems']):
                st = parse(thms[name]['runner_statement'])
                if st and st['shape'] == 2 and {st['S'], st['R']} == {other, row['rule']} and st['hyp'] == ('ge', 0):
                    record(name, 'MATCH', f"Table 2 {row['a_number']}, Rule {other} = Rule {row['rule']}, all n"
                           + (' (statement: at every stage g, stronger)' if st.get('every_stage') else ''))
                elif st and st['shape'] == 2 and {st['S'], st['R']} == {other, row['rule']}:
                    record(name, 'MISMATCH', f"hypothesis {st['hyp']} not in table")
                else:
                    record(name, 'MISMATCH' if st else 'UNTEMPLATED', f"Table 2 {row['a_number']}, Rule {other}")
        elif row['table'] == 'relations':
            for name in [t.strip() for t in row['theorem'].split(',')]:
                st = parse(thms[name]['runner_statement'])
                a, b = (row['rules'] + [None])[:2]
                if row['kind'] == 'ge2' and st and st['shape'] == 2:
                    ok = (st['S'], st['R']) == (a, b) and st['hyp'] == ('ge', 2)
                    record(name, 'MATCH' if ok else 'MISMATCH', f"Table 3 {row['a']}: c_{a}(n)=c_{b}(n), n>=2")
                elif row['kind'] == 'iff' and st and st.get('kind') == 'iff':
                    ok = (st['S'], st['R'], st['k']) == (a, b, 1)
                    record(name, 'MATCH' if ok else 'MISMATCH', f"Table 3 {row['a']}: c_{a}(n)=c_{b}(n) iff n!=1")
                elif row['kind'] == 'iff' and st and st['shape'] == 1:
                    f = lambda n: Fraction((2 ** (n + 1) - 1) ** 2)
                    ok = st['R'] == a and st['hyp'] == ('ne', 1) and not same_function(st, f, 0)
                    record(name, 'MATCH' if ok else 'MISMATCH', f"Table 3 {row['a']}: c_{a}(n)=(2^(n+1)-1)^2, n!=1")
                elif name == 'LT2D.a060867_r737_exception':
                    s = ' '.join(thms[name]['runner_statement'].split())
                    ok = s == 'LT2D.onCount 737 (2 ^ 1 - 1) = 4'
                    record(name, 'MATCH' if ok else 'MISMATCH', 'Table 3 A060867: c_737(1)=4')
                else:
                    record(name, 'READ', f"Table 3 {row['a']}: kind {row['kind']}")
    for name, (kind, R, x, f, where) in MAIN.items():
        st = parse(thms[name]['runner_statement'])
        if kind == 'closed':
            ok = st and st['shape'] == 1 and st['R'] == R and st['hyp'] == ('ge', x) and not same_function(st, f, x)
        else:
            ok = st and st['shape'] == 3 and (st['S'], st['R']) == (R, x)
        record(name, 'MATCH' if ok else 'MISMATCH', where)
    for name in thms:
        if name not in seen:
            record(name, 'READ', 'main text')

    from collections import Counter
    c = Counter(s for _, s, _ in results)
    print(f"{len(results)} top-level theorems: " + ', '.join(f"{c[k]} {k}" for k in
          ['MATCH', 'MISMATCH', 'UNTEMPLATED', 'READ'] if c[k]), file=out)
    print(file=out)
    for name, status, note in results:
        print(f"{status:11} {name}  ({note})", file=out)
        if status in ('READ', 'UNTEMPLATED', 'MISMATCH'):
            print('            ' + ' '.join(thms[name]['runner_statement'].split()), file=out)
    if missing := [n for n in thms if n not in {r[0] for r in results}]:
        print('missing:', missing, file=out)


if __name__ == '__main__':
    main()
