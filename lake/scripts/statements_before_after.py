"""Compare each top-level theorem's statement in this build with the statement the Long Table runner reported.

The statements are printed with scripts/Report.lean (the runner's ReportImports.lean, prefix LT2D): each module's
LT2D.* imports are replaced by their own imports, so only core and Mathlib are loaded when printing. Post-module
names (LongTable.P_<id>) do not occur in statements; the mapping below handles any that would, and the one
renamed helper (D1 -> D1_r641). Writes statements_before_after.txt; exits 1 on any difference."""
import json, os, re, subprocess, sys
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
man = json.load(open("manifest.json"))
p2m = {m["post_id"]: m["module"] for m in man["modules"]}
def map_old(s):
    s = re.sub(r"LongTable\.P_([a-z0-9]+)_([a-z0-9]+)", lambda m: p2m[m.group(1) + "-" + m.group(2)], s)
    return s
by_mod = {}
for t in man["top_level_theorems"]:
    by_mod.setdefault(t["module"], []).append(t)
lines, diffs, missing = [], 0, 0
for mod in sorted(by_mod):
    r = subprocess.run(["lake", "env", "lean", "--run", "scripts/Report.lean", "statements", mod],
                       capture_output=True, text=True)
    if r.returncode:
        sys.stderr.write(r.stderr); sys.exit(2)
    got = {x["name"]: x["statement"] for x in json.loads(r.stdout.strip().splitlines()[-1])["statements"]}
    for t in by_mod[mod]:
        old = map_old(t["runner_statement"]); new = got.get(t["name"])
        if new is None:
            missing += 1; status = "MISSING"
        elif new == old:
            status = "MATCH"
        else:
            diffs += 1; status = "DIFFERENT"
        lines.append(f"{status}  {t['name']}  ({mod}, post #{t['post_id']})")
        if status != "MATCH":
            lines.append(f"    runner: {old}\n    build:  {new}")
n = len(man["top_level_theorems"])
summary = f"{n} top-level theorems: {n - diffs - missing} match, {diffs} differ, {missing} missing"
open("statements_before_after.txt", "w").write(summary + "\n\n" + "\n".join(lines) + "\n")
print(summary)
sys.exit(1 if diffs or missing else 0)
