"""Each of the seven LT2D definitions occurs exactly once in the project, in LT2D/Defs.lean.
Declarations are found with leandecls.py, which skips comments, strings and docstrings."""
import glob, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leandecls
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
want = {"LT2D.caState": "def", "LT2D.onCount": "def", "LT2D.window": "def", "LT2D.ruleOut": "def",
        "LT2D.nbrOn": "def", "LT2D.step": "def", "LT2D.Cell": "abbrev"}
found = {n: [] for n in want}
for f in sorted(glob.glob(os.path.join(root, "LT2D/**/*.lean"), recursive=True)) + [os.path.join(root, "All.lean")]:
    for full, kw, priv, line in leandecls.declarations(open(f, encoding="utf-8").read()):
        if full in found:
            found[full].append((os.path.relpath(f, root), kw, line, priv))
ok = True
for n, kw in want.items():
    locs = found[n]
    good = len(locs) == 1 and locs[0][0] == "LT2D/Defs.lean" and locs[0][1] == kw and not locs[0][3]
    ok &= good
    print(f"{'OK  ' if good else 'FAIL'} {kw} {n}: {len(locs)} occurrence(s) " + "; ".join(f"{p}:{l}" for p, _, l, _ in locs))
# every other declared name: at most one public declaration in the whole project
seen = {}
for f in sorted(glob.glob(os.path.join(root, "LT2D/**/*.lean"), recursive=True)):
    for full, kw, priv, line in leandecls.declarations(open(f, encoding="utf-8").read()):
        if not priv:
            seen.setdefault(full, []).append(os.path.relpath(f, root))
dups = {k: v for k, v in seen.items() if len(v) > 1}
for k, v in sorted(dups.items()):
    print(f"FAIL duplicate public declaration {k}: {', '.join(v)}")
ok &= not dups
print("unique definitions: " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
