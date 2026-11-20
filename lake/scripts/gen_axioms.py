"""Write axioms.lean (#print axioms for every top-level theorem), run it, save axioms.txt, and fail unless every
theorem depends on propext, Classical.choice and Quot.sound only."""
import json, os, re, subprocess, sys
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
man = json.load(open("manifest.json"))
names = [t["name"] for t in man["top_level_theorems"]]
open("axioms.lean", "w").write("import All\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
r = subprocess.run(["lake", "env", "lean", "axioms.lean"], capture_output=True, text=True)
out = r.stdout + r.stderr
open("axioms.txt", "w").write(out)
allowed = {"propext", "Classical.choice", "Quot.sound"}
ok = r.returncode == 0
found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
nodeps = re.findall(r"'([^']+)' does not depend on any axioms", out)
seen = {n for n, _ in found} | set(nodeps)
for n, axs in found:
    extra = {a.strip() for a in axs.split(",")} - allowed
    if extra:
        ok = False; print(f"FAIL {n}: {sorted(extra)}")
for n in names:
    if n not in seen:
        ok = False; print(f"FAIL {n}: no #print axioms output")
print(f"{len(names)} theorems; axioms within propext, Classical.choice, Quot.sound: " + ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)
