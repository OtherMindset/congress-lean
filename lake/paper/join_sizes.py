#!/usr/bin/env python3
"""Join the table list (table_sizes.py), the product sizes (output of Sizes.lean) and build_report.csv into
table_sizes.json, the input of gen_sizes_tex.py.

Usage, from lake/: python3 -I paper/join_sizes.py /tmp/tables.json paper/Sizes_output.txt build_report.csv \
                     paper/table_sizes.json
"""
import csv
import json
import os
import re
import sys

tables_json, sizes_out, report, out = sys.argv[1:5]
lake = os.path.dirname(os.path.abspath(report))
t = {v['ns']: v for v in json.load(open(tables_json))}
for m in re.finditer(r'\("(VN\.\w+)", (\d+), (\d+)\)', open(sizes_out).read()):
    t[m[1]]['seed'], t[m[1]]['step'] = int(m[2]), int(m[3])
for v in t.values():
    if v.get('chunked'):
        assert v['step'] == sum(v['slices']), v['ns']  # the chunks cover exactly the explored product
B = {r['module']: (float(r['seconds']), int(r['peak_rss_mb'])) for r in csv.DictReader(open(report))}


def mod(p):
    return p[:-5].replace('/', '.')


for v in t.values():
    tf = v['tab_file']
    files = v['files']
    core, d = mod(tf), os.path.dirname(tf)
    steps = [mod(f) for f in files if os.path.basename(f).startswith('D')]
    m = mod(d + '/M.lean') if os.path.exists(os.path.join(lake, d, 'M.lean')) else None
    v.update(core_mod=core, step_mods=steps, m_mod=m, t_core=B[core][0], t_step=sum(B[s][0] for s in steps),
             t_m=B[m][0] if m else None,
             mem=max([B[core][1]] + [B[s][1] for s in steps] + ([B[m][1]] if m else [])),
             group=tf.startswith('LT2D/Groups/'))
json.dump(sorted(t.values(), key=lambda v: (v['R'], v['ns'])), open(out, 'w'), indent=1)
print(len(t), 'tables')
