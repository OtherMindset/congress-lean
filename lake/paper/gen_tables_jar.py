#!/usr/bin/env python3
"""Generate the paper's tables from structured row data + results.csv.

c_R(n) := number of ON cells of rule R in the (2g+1)-square at stage g = 2^n - 1
          (LT2D.onCount R (2^n - 1)).
Closed forms are stored as (n0, R, A, B, C, D, sh):  16*D*c_R(n) = A*4^n + B*2^n + C  for n >= n0,
and the OEIS entry's a(n + sh) = c_R(n)  (sh = 0 except index-shifted Price comments).
Every row is (1) looked up in results.csv by its Lean theorem name, to take the ledger id
from there, and (2) re-checked against data/sim_n9.json (independent numpy simulator)
for n0 <= n <= 9.  The script stops on any mismatch.
"""
import csv, json, sys, os
from fractions import Fraction
ROOT = os.path.abspath(sys.argv[1])   # folder with results.csv, sim_n9.json, sim_extra_n9.json
OUT = os.path.abspath(sys.argv[2])    # folder for tables.tex, appendix_index.tex, rows.json

rows = list(csv.DictReader(open(os.path.join(ROOT, 'results.csv'))))
# PATCH (20 Nov 2026 draft): A273331 / Rule 654 reproved by the digit-automaton method on LT2D.caState.
# Ledger id and theorem names are taken from the 20 Nov PDF draft; replace by the refreshed ledger export.
if not any(r['ledger_id']=='l-mwosy0fw-2q4ogh' for r in rows):
    rows.append({'ledger_id':'l-mwosy0fw-2q4ogh','a_number':'A273331','rules':'654','lean_theorems':'LT2D.a273331_formula, LT2D.a273331_a16','runner':'passed (machine-checked) [from 20 Nov draft; CSV row pending]'})
def ledger_of(thm):
    hits = [r for r in rows if thm in [t.strip() for t in r['lean_theorems'].split(',')]]
    if not hits:
        sys.exit('theorem not in results.csv: ' + thm)
    return hits[0]

# (A-number, theorem, (n0, R, A, B, C, D, sh), who conjectured / source line)
FORMULAS = [
 ("A269907","LT2D.a269907_formula",(1,1,64,-64,-64,1,0),"Barker 2016"),
 ("A269911","LT2D.a269911_formula",(1,3,64,-64,-48,1,0),"Barker 2016"),
 ("A269696","LT2D.a269696_formula",(1,6,20,0,0,1,0),"Barker 2016"),
 ("A060867","LT2D.a060867_r7_formula",(0,7,64,-64,16,1,1),"Price 2016"),
 ("A269712","LT2D.a269712_formula",(1,20,0,64,-64,1,0),"Barker 2016"),
 ("A269716","LT2D.a269716_formula",(2,22,24,-16,0,1,0),"Barker 2016"),
 ("A269815","LT2D.a269815_formula",(1,35,56,-80,16,1,0),"Blomberg 2016"),
 ("A270080","LT2D.a270080_formula",(3,62,16,32,-128,1,0),"Blomberg 2016"),
 ("A270084","LT2D.a270084_formula",(2,65,64,-160,192,1,0),"Blomberg 2016"),
 ("A270088","LT2D.a270088_formula",(3,73,64,-64,16,1,0),"Blomberg 2016"),
 ("A270126","LT2D.a270126_formula",(2,86,24,0,0,1,0),"Barker 2016"),
 ("A270130","LT2D.a270130_formula",(3,89,64,-64,16,1,0),"Blomberg 2016"),
 ("A270165","LT2D.a270165_formula",(4,107,56,-48,16,1,0),"Blomberg 2016"),
 ("A270218","LT2D.a270218_formula",(1,129,128,-192,64,3,0),"Barker 2016"),
 ("A270222","LT2D.a270222_formula",(1,131,48,-64,16,1,0),"Barker 2016"),
 ("A270287","LT2D.a270287_formula",(3,145,47,-64,16,1,0),"Blomberg 2016"),
 ("A270682","LT2D.a270682_formula",(2,190,16,64,-128,1,0),"Blomberg 2016"),
 ("A270935","LT2D.a270935_formula",(2,221,64,-64,-64,1,0),"Blomberg 2016"),
 ("A271005","LT2D.a271005_formula",(3,245,64,-96,0,1,0),"Blomberg 2016"),
 ("A271055","LT2D.a271055_formula",(2,259,64,-64,-192,1,0),"Blomberg 2016"),
 ("A271061","LT2D.a271061_formula",(1,261,64,-64,0,1,0),"Blomberg 2016"),
 ("A271092","LT2D.a271092_formula",(2,275,64,-64,-128,1,0),"Blomberg 2016"),
 ("A271254","LT2D.a271254_formula",(2,323,64,-160,192,1,0),"Blomberg 2016"),
 ("A271286","LT2D.a271286_r337_formula",(1,337,176,-192,-128,3,0),"Barker 2016"),
 ("A272417","LT2D.a272417_formula",(0,469,176,-192,64,3,0),"Barker 2016"),
 ("A272586","LT2D.a272586_formula",(2,507,176,-192,-128,3,0),"Blomberg 2016"),
 ("A092440","LT2D.a092440_r510_formula",(0,510,32,-32,16,1,0),"Price 2016"),
 ("A059153","LT2D.a059153_r513_formula_shifted",(1,513,32,-32,0,1,-1),"Price 2016"),
 ("A272706","LT2D.a272706_formula",(1,515,48,-128,144,1,0),"Blomberg 2016"),
 ("A272743","LT2D.a272743_formula",(2,526,52,0,-16,3,0),"Blomberg 2016"),
 ("A273145","LT2D.a273145_formula",(2,597,56,-64,16,1,0),"Blomberg 2016"),
 ("A002450","LT2D.a002450_r598_formula_shifted",(0,598,64,0,-16,3,1),"Price 2016"),
 ("A273251","LT2D.a273251_formula",(1,619,160,-192,-16,3,0),"Blomberg 2016"),
 ("A273310","LT2D.a273310_formula",(2,641,64,-64,-128,1,0),"Blomberg 2016"),
 ("A273313","LT2D.a273313_formula",(2,643,64,-64,-112,1,0),"Blomberg 2016"),
 ("A273331","LT2D.a273331_formula",(3,654,53,0,-80,3,0),"Blomberg 2016"),
 ("A273335","LT2D.a273335_formula",(2,657,64,-64,0,1,0),"Barker 2016"),
 ("A273385","LT2D.a273385_rule659",(2,659,64,-64,16,1,0),"Blomberg 2016"),
 ("A273418","LT2D.a273418_formula",(2,705,64,-64,-112,1,0),"Blomberg 2016"),
 ("A273446","LT2D.a273446_formula",(3,721,64,-64,0,1,0),"Blomberg 2016"),
 ("A165665","LT2D.a165665_r773_formula",(0,773,48,-32,0,1,0),"Price 2016"),
 ("A273539","LT2D.a273539_formula",(0,779,64,-128,80,1,0),"Barker 2016"),
 ("A273565","LT2D.a273565_formula",(2,793,43,-64,16,1,0),"Blomberg 2016"),
 ("A273570","LT2D.a273570_formula",(2,798,32,-96,208,1,0),"Blomberg 2016"),
 ("A273676","LT2D.a273676_formula",(2,833,48,-64,16,1,0),"Blomberg 2016"),
 ("A273767","LT2D.a273767_formula",(3,913,64,-64,16,1,0),"Blomberg 2016"),
 ("A273750","LT2D.r926_count",(0,926,64,0,-16,3,0),"none stated"),
 ("A273828","LT2D.a273828_formula",(3,950,32,-32,-48,1,0),"Blomberg 2016"),
 ("A273832","LT2D.a273832_formula",(2,961,64,-64,-48,1,0),"Blomberg 2016"),
 ("A273848","LT2D.a273848_formula",(3,969,64,-64,16,1,0),"Blomberg 2016"),
]
# Rows that are runner-built but NOT machine-checked on the ledger (no cross-family statement match yet)
PENDING_FORMULAS = []  # A270222 (R131) and A273750 (R926) moved to FORMULAS after the 20 Nov 2026 ledger upgrade

# Equal-count families: (A-number, base rule, [other rules], range, theorem prefix list) -- c_S(n) = c_R(n)
EQUAL = [
 ("A269696",6,[38,70,102,134,166,198,230],0),
 ("A269712",20,[28,52,60,148,156,180,188,532,540,564,572,660,668,692,700],0),
 ("A269815",35,[43,59],0),
 ("A270084",65,[321],0),
 ("A270126",86,[342],0),
 ("A270218",129,[385,425,465,553],0),
 ("A270222",131,[163,171,227,235,771,787,803,811,819,827,835,851,867,875,883,891],0),
 ("A270287",145,[153],0),
 ("A270682",190,[254],0),
 ("A270935",221,[253],0),
 ("A271005",245,[501],0),
 ("A271061",261,list(range(269,382,8))+[413,445,477,509]+list(range(645,766,8)),0),
 ("A271286",337,[505],0),
 ("A272706",515,[523],0),
 ("A273251",619,[635],0),
 ("A273310",641,[649,897,905],0),
 ("A273313",643,[651,707,715],0),
 ("A273335",657,[665],0),
 ("A273385",659,[667,723,731,931,939,947,955,995,1003,1011,1019],0),
 ("A273418",705,[713],0),
 ("A273446",721,[729],0),
 ("A273539",779,[795,843,859],0),
 ("A273570",798,[862],0),
 ("A273676",833,[849],0),
 ("A273767",913,[921,929,937,945,953],0),
 ("A273750",926,[990],0),
 ("A273828",950,[1014],0),
 ("A273832",961,[977],0),
 ("A273848",969,[985],0),
]
# theorem names for the equal-count rows, from results.csv (searched by rule number)
ALLSTAGE = {'A273750'}  # entry counts every stage n; the row gives a(2^n-1) = c_R(n)
EQUAL_THEOREMS = {"A273750": ["LT2D.r990_count_eq_926"]}
def equal_theorems(anum, base, others):
    if anum in EQUAL_THEOREMS:
        return EQUAL_THEOREMS[anum]
    names = []
    for r in rows:
        for t in [t.strip() for t in r['lean_theorems'].split(',')]:
            low = t.lower()
            if anum.lower() in low and any((f"_r{s}_" in low) or low.endswith(f"_rule{s}") or (f"_r{s}" == low[-len(f'_r{s}'):]) or (f"rule{s}" in low and f"rule{s}" == low.split('_')[-1]) for s in others):
                if t not in names and 'formula' not in low:
                    names.append(t)
    return names

# Relations between sequences (pairs of rules), from the ledger claims
RELATIONS = [
 ("A273832","A269911",961,3,"ge2","LT2D.a273832_eq_a269911"),
 ("A273676","A270222",833,131,"ge2","LT2D.a273676_eq_a270222"),
 ("A270935","A269907",221,1,"ge2","LT2D.a270935_eq_a269907"),
 ("A273418","A273313",705,643,"ge2","LT2D.a273418_eq_a273313"),
 ("A273310","A271092",641,275,"iff","LT2D.a273310_eq_a271092_iff"),
 ("A273335","A271061",657,261,"iff","LT2D.a273335_eq_a271061_iff"),
 ("A272586","A271286",507,505,"iff","LT2D.a272586_eq_rule505_iff"),
 ("A060867","A060867",737,7,"iff","LT2D.a060867_r737_formula, LT2D.a060867_r737_exception"),
 ("A270218","A006095",129,None,"a006095","LT2D.a270218_eq_four_a006095"),
]
EXTRA_LEDGER = {"LT2D.a270218_eq_four_a006095": "l-mwnxxkok-8udtr8"}

sim = json.load(open(os.path.join(ROOT, 'sim_n9.json')))
EXTRA = os.path.join(ROOT, 'sim_extra_n9.json')
extra = json.load(open(EXTRA)) if os.path.exists(EXTRA) else {}
def simc(R, n):
    v = sim.get(str(R)) or extra.get(str(R))
    if v is None:
        return None   # no simulation data for this rule: reported as an error below
    return v[n] if n < len(v) else None

def cval(F, n):
    n0, R, A, B, C, D, sh = F
    num = A * 4**n + B * 2**n + C
    assert num % (16 * D) == 0, (F, n)
    return num // (16 * D)

def tex_formula(F):
    n0, R, A, B, C, D, sh = F
    coefs = [Fraction(A, 16*D), Fraction(B, 16*D), Fraction(C, 16*D)]
    three = any(q.denominator % 3 == 0 for q in coefs)
    if three:
        coefs = [q*3 for q in coefs]
    parts = []
    for q, base, step in zip(coefs, ('4', '2', None), (4, 2, None)):
        if q == 0:
            continue
        if base is None:
            assert q.denominator == 1, F
            parts.append((int(q), str(abs(int(q)))))
            continue
        j = 0
        while q.denominator != 1:
            q *= step; j += 1
        assert q.denominator == 1, F
        e = f'{base}^{{n}}' if j == 0 else f'{base}^{{n-{j}}}'
        m = abs(int(q))
        parts.append((int(q), e if m == 1 else f'{m}\\cdot {e}'))
    out = ''
    for k, (v, body) in enumerate(parts):
        if k == 0:
            out += ('-' if v < 0 else '') + body
        else:
            out += (' - ' if v < 0 else ' + ') + body
    if three:
        return f'\\tfrac{{1}}{{3}}\\bigl({out}\\bigr)'
    return out

def tt(name):
    return '\\texttt{' + name.replace('_', '\\_\\allowbreak{}').replace('.', '.\\allowbreak{}') + '}'
errors = []
out = []
out.append('% GENERATED by tools/gen_tables_jar.py (adapted from paper/gen_tables.py) from results.csv and the row data in that script. Do not edit by hand.')
# ---------- Table 1 ----------
out.append(r'\begin{small}\begin{longtable}{@{}l r >{\raggedright}p{3.9cm} c >{\raggedright\arraybackslash}p{4.0cm}@{}}')
out.append(r'\caption{Closed forms proved for all $n\ge n_0$: $c_R(n)$ is the number of ON cells of rule $R$ in $[-g,g]^2$ at stage $g=2^n-1$. The entry is $a(n+s)=c_R(n)$ with $s=0$ unless marked; the row marked $[a(2^n{-}1)]$ is an entry that counts every stage $n$, and there $a(2^n-1)=c_R(n)$. Closed forms are written with powers $4^{n-j}$ where that keeps integer coefficients. Ledger entries are listed in Appendix~\ref{app:index}.}\label{tab:formulas}\\')
out.append(r'\toprule A-number & $R$ & $c_R(n)$ & $n_0$ & Lean theorem\\ \midrule\endfirsthead')
out.append(r'\toprule A-number & $R$ & $c_R(n)$ & $n_0$ & Lean theorem\\ \midrule\endhead')
records = []
for anum, thm, F, who in FORMULAS:
    r = ledger_of(thm)
    n0, R, A, B, C, D, sh = F
    for n in range(n0, 10):
        s = simc(R, n)
        if s is None:
            errors.append(f'{anum}: no sim for rule {R}')
            break
        if s != cval(F, n):
            errors.append(f'{anum} R{R} n={n}: formula {cval(F,n)} sim {s}')
    if 'machine-checked' not in r['runner'] and 'passed' not in r['runner']:
        errors.append(f'{anum}: runner field {r["runner"]}')
    shift = '' if sh == 0 else (f' $[s={sh:+d}]$')
    if anum in ALLSTAGE: shift += ' $[a(2^n{-}1)]$'
    out.append(f'\\seqnum{{{anum}}}{shift} & {R} & ${tex_formula(F)}$ & {n0} & {tt(thm)}\\\\')
    records.append(dict(table='formulas', a_number=anum, rule=R, n0=n0, A=A, B=B, C=C, D=D, shift=sh,
                        latex=tex_formula(F), theorem=thm, ledger_id=r['ledger_id'], source=who))
out.append(r'\bottomrule\end{longtable}\end{small}')

# ---------- Table 2 ----------
out.append(r'\begin{small}\begin{longtable}{@{}l r >{\raggedright\arraybackslash}p{8.4cm}@{}}')
out.append(r'\caption{Rules proved to have the same count as the rule of the entry $R$ at every stage $2^n-1$, $n\ge0$ ($c_S(n)=c_R(n)$ for each listed $S$). Each listed rule $S$ is a separate Lean theorem; names and ledger entries are listed in Appendix~\ref{app:index}.}\label{tab:equal}\\')
out.append(r'\toprule A-number & $R$ & other rules $S$\\ \midrule\endfirsthead')
out.append(r'\toprule A-number & $R$ & other rules $S$\\ \midrule\endhead')
nrules = set()
for anum, base, others, n0 in EQUAL:
    nrules.add(base); nrules.update(others)
    for S in others:
        for n in range(0, 10):
            if simc(S, n) != simc(base, n):
                errors.append(f'{anum}: rule {S} vs {base} differ at n={n}')
    th = equal_theorems(anum, base, others)
    lids = sorted({ledger_of(t)['ledger_id'] for t in th})
    if len(th) != len(others):
        errors.append(f'{anum}: found {len(th)} theorems for {len(others)} rules: {th}')
    out.append(f'\\seqnum{{{anum}}} & {base} & {", ".join(map(str, others))}\\\\')
    records.append(dict(table='equal', a_number=anum, rule=base, others=others, theorems=th, ledger_ids=lids))
out.append(r'\bottomrule\end{longtable}\end{small}')

# ---------- Table 3 ----------
out.append(r'\begin{small}\begin{longtable}{@{}>{\raggedright}p{1.35cm} >{\raggedright}p{1.35cm} l >{\raggedright}p{3.4cm} >{\raggedright\arraybackslash}p{3.0cm}@{}}')
out.append(r'\caption{Relations between sequences (comments by Mathar, Blomberg, Price and Stajszczak). In the last row the OEIS sequence A006095 enters through its closed form $(2^n-1)(2^{n-1}-1)/3$, as defined in the Lean file.}\label{tab:relations}\\')
out.append(r'\toprule entry & compared with & rules & statement proved & Lean theorem\\ \midrule\endfirsthead')
out.append(r'\toprule entry & compared with & rules & statement proved & Lean theorem\\ \midrule\endhead')
for a1, a2, R1, R2, kind, thm in RELATIONS:
    first = thm.split(',')[0].strip()
    r = {'ledger_id': EXTRA_LEDGER[first]} if first in EXTRA_LEDGER else ledger_of(first)
    if kind == 'a006095':
        for n in range(1, 10):
            a6 = (2**(n+1) - 1) * (2**n - 1) // 3
            if simc(R1, n) != 4 * a6: errors.append(f'{thm}: n={n}')
        st = f'$c_{{129}}(n)=4\\,\\mathrm{{A006095}}(n+1)$ for $n\\ge1$, with A006095 given by its closed form'
        out.append(f'\\seqnum{{{a1}}} & \\seqnum{{{a2}}} & 129 & {st} & {tt(thm)}\\\\')
        records.append(dict(table='relations', a=a1, b=a2, rules=[R1], kind=kind, theorem=thm, ledger_id=r['ledger_id']))
        continue
    for n in range(0, 10):
        eq = simc(R1, n) == simc(R2, n)
        want = (n >= 2) if kind == 'ge2' else (n != 1)
        if kind == 'ge2' and n >= 2 and not eq: errors.append(f'{thm}: n={n} not equal')
        if kind == 'iff' and eq != want: errors.append(f'{thm}: n={n} eq={eq}')
    if kind == 'ge2':
        st = f'$c_{{{R1}}}(n)=c_{{{R2}}}(n)$ for $n\\ge2$'
    else:
        st = f'$c_{{{R1}}}(n)=c_{{{R2}}}(n)\\iff n\\ne1$'
        if thm.endswith('exception'):
            st = f'$c_{{737}}(n)=(2^{{n+1}}-1)^2$ for $n\\ne1$, $c_{{737}}(1)=4$'
    out.append(f'\\seqnum{{{a1}}} & {("\\seqnum{"+a2+"}") if a2!=a1 else "Rule 7"} & {R1}, {R2} & {st} & {", ".join(tt(t.strip()) for t in thm.split(","))}\\\\')
    records.append(dict(table='relations', a=a1, b=a2, rules=[R1, R2], kind=kind, theorem=thm, ledger_id=r['ledger_id']))
out.append(r'\bottomrule\end{longtable}\end{small}')

# ---------- pending ----------
pend = []
for anum, thm, F, who, post, lid in PENDING_FORMULAS:
    n0, R, *_ = F
    for n in range(n0, 10):
        if simc(R, n) is not None and simc(R, n) != cval(F, n):
            errors.append(f'pending {anum}: n={n}')
    pend.append(dict(table='pending', a_number=anum, rule=R, n0=n0, latex=tex_formula(F), theorem=thm, post=post, ledger_id=lid,
                     A=F[2], B=F[3], C=F[4], D=F[5]))
records += pend

allrules = set(F[1] for _, _, F, _ in FORMULAS) | nrules | {737}
stats = dict(formula_rows=len(FORMULAS), entries=len({a for a, *_ in FORMULAS}), equal_rows=len(EQUAL),
             equal_rules=sum(len(o) for _, _, o, _ in EQUAL), relations=len(RELATIONS), rules_total=len(allrules))
open(os.path.join(OUT, 'tables.tex'), 'w').write('\n'.join(out) + '\n')
json.dump(dict(stats=stats, rows=records), open(os.path.join(OUT, 'rows.json'), 'w'), indent=1)
idx = ['% GENERATED by tools/gen_tables_jar.py. Do not edit by hand.',
       r'\begin{footnotesize}\begin{longtable}{@{}l >{\raggedright}p{1.2cm} l >{\raggedright\arraybackslash}p{5.0cm} >{\raggedright\arraybackslash}p{2.6cm}@{}}',
       r'\caption{Artifact index: for each row of Tables~\ref{tab:formulas}--\ref{tab:relations}, the Lean theorems and the entry of the public ledger that records the build report and the statement checks.}\label{tab:index}\\',
       r'\toprule Table & $R$ & entry & Lean theorems & ledger entry\\ \midrule\endfirsthead',
       r'\toprule Table & $R$ & entry & Lean theorems & ledger entry\\ \midrule\endhead']
for rec in records:
    if rec['table'] == 'formulas':
        idx.append(f"\\ref{{tab:formulas}} & {rec['rule']} & {rec['a_number']} & {tt(rec['theorem'])} & \\texttt{{{rec['ledger_id']}}}\\\\")
    elif rec['table'] == 'equal':
        idx.append(f"\\ref{{tab:equal}} & {rec['rule']} & {rec['a_number']} & " + ', '.join(tt(t) for t in rec['theorems']) + ' & ' + r'\newline '.join(f'\\texttt{{{l}}}' for l in rec['ledger_ids']) + r'\\')
    elif rec['table'] == 'relations':
        idx.append(f"\\ref{{tab:relations}} & {', '.join(str(x) for x in rec['rules'])} & {rec['a']} & " + ', '.join(tt(t.strip()) for t in rec['theorem'].split(',')) + f" & \\texttt{{{rec['ledger_id']}}}\\\\")
idx.append(r'\bottomrule\end{longtable}\end{footnotesize}')
open(os.path.join(OUT, 'appendix_index.tex'), 'w').write('\n'.join(idx) + '\n')
print(json.dumps(stats))
if errors:
    print('ERRORS:'); print('\n'.join(errors)); sys.exit(1)
print('ok: every formula and relation agrees with data/sim_n9.json; every theorem found in results.csv')
