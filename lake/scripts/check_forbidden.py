"""No `sorry`, `native_decide`, `axiom` or `implemented_by` outside comments and strings, in any Lean file of
the project (the scripts' own Report.lean, which uses none of them, is checked too)."""
import glob, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leandecls
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
pat = re.compile(r"(?<![\w.'])(sorry|native_decide|axiom|implemented_by)(?![\w'])")
bad = 0
files = sorted(glob.glob(os.path.join(root, "**/*.lean"), recursive=True))
files = [f for f in files if "/.lake/" not in f]
for f in files:
    s = leandecls.strip(open(f, encoding="utf-8").read())
    for m in pat.finditer(s):
        bad += 1
        print(f"FAIL {os.path.relpath(f, root)}:{s.count(chr(10), 0, m.start()) + 1}: {m.group(1)}")
print(f"{len(files)} files checked; forbidden tokens: {bad} -> " + ("PASS" if bad == 0 else "FAIL"))
sys.exit(1 if bad else 0)
