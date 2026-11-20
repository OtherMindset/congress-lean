#!/usr/bin/env python3
"""Collect every guessed table of the VN library in the artifact, with what its certificates use.

Usage: python3 -I table_sizes.py <lake_dir> <out_json> <out_lean>
For each table: file, namespace, Q (states), the rule R and mask U of its step check, whether that check is chunked
(and the slice sizes, which add up to the step product), the counting check (checkRec, degree 3, or checkRecX with
polynomial p, degree len(p)), and the twin rules it certifies. Writes a Lean file that recomputes the seed and step
product sizes with the library's own functions (VN.explore with VN.fuel) by #eval, for comparison.
"""
import glob
import json
import os
import re
import sys

lake, out_json, out_lean = sys.argv[1:4]
tables = {}
files = sorted(glob.glob(os.path.join(lake, 'LT2D/**/*.lean'), recursive=True))
for path in files:
    rel = os.path.relpath(path, lake)
    if rel.startswith('LT2D/VN/'):
        continue
    src = open(path).read()
    for blk in re.finditer(r'namespace (VN\.\w+)\n(.*?)\nend \1', src, re.S):
        ns, body = blk[1], blk[2]
        t = tables.setdefault(ns, {'ns': ns, 'files': []})
        t['files'].append(rel)
        m = re.search(r'def tab : Tab := ⟨\[(.*?)\], \[([0-9,\s]*)\], by decide \+kernel⟩', body, re.S)
        if m:
            rows = re.findall(r'\[([0-9,\s]*)\]', m[1])
            t['T'] = [[int(v) for v in r.split(',')] for r in rows]
            t['O'] = [int(v) for v in m[2].split(',')]
            t['Q'] = len(t['T'])
            t['tab_file'] = rel
        for m in re.finditer(r'checkF1 tab (\d+) (\d+) = true', body):
            t['R'], t['U'], t['chunked'] = int(m[1]), int(m[2]), False
        for m in re.finditer(r'sliceOK tab (\d+) (\d+) ', body):
            t['R'], t['U'], t['chunked'] = int(m[1]), int(m[2]), True
        sl = [int(v) for v in re.findall(r'def s\w* : List P1 := unpack \d+ (\d+) ', body)]
        if sl:
            t.setdefault('slices', []).extend(sl)
        m = re.search(r'checkRecX tab \[([-0-9,\s]*)\]', body)
        if m:
            t['rec'] = 'checkRecX'
            t['deg'] = len(m[1].split(','))
        elif re.search(r'checkRec tab ', body):
            t['rec'], t['deg'] = 'checkRec', 3
        m = re.search(r'theorem twins : \[([0-9,\s]*)\]', body)
        if m:
            t['twins'] = [int(v) for v in m[1].split(',')]
tables = {k: v for k, v in tables.items() if 'T' in v}
for v in tables.values():
    if v.get('chunked'):
        v['step_from_slices'] = sum(v.get('slices', []))
json.dump(sorted(tables.values(), key=lambda v: (v.get('R', -1), v['ns'])), open(out_json, 'w'), indent=1)

L = ['import LT2D.VN.K9', 'import LT2D.VN.K8', 'open VN', '']
for i, v in enumerate(sorted(tables.values(), key=lambda v: v['ns'])):
    T = '[' + ',\n  '.join('[' + ','.join(map(str, r)) + ']' for r in v['T']) + ']'
    L.append(f'def tab{i} : Tab := ⟨{T}, [{",".join(map(str, v["O"]))}], by decide +kernel⟩')
    L.append(f'#eval ("{v["ns"]}", (explore key2 (step2 tab{i}) fuel [start2] .leaf).toList.length, '
             f'(explore key1 (step1 tab{i}) fuel [start1] .leaf).toList.length)')
open(out_lean, 'w').write('\n'.join(L) + '\n')
print(len(tables), 'tables')
