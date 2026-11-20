"""Build every module of the project one at a time in import order and write build_report.csv
(module, seconds, peak_rss_mb, exit). Continues past failures so every failure is reported."""
import os, re, subprocess, sys, glob
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
files = sorted(glob.glob("LT2D/**/*.lean", recursive=True)) + ["All.lean"]
mods = {f[:-5].replace("/", "."): f for f in files}
deps = {m: [i for i in re.findall(r"^import (\S+)", open(f).read(), re.M) if i in mods] for m, f in mods.items()}
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps[m]: visit(d)
    order.append(m)
for m in sorted(mods): visit(m)
out = sys.argv[1] if len(sys.argv) > 1 else "build_report.csv"
failed = set()
os.makedirs("build_errors", exist_ok=True)
with open(out, "w") as f:
    f.write("module,seconds,peak_rss_mb,exit\n")
    for m in order:
        if any(d in failed for d in deps[m]):
            f.write(f"{m},,,skipped (an import failed)\n"); f.flush(); failed.add(m); continue
        r = subprocess.run([sys.executable, "scripts/build_one.py", m], capture_output=True, text=True)
        f.write(r.stdout); f.flush()
        if r.returncode:
            failed.add(m)
            open(f"build_errors/{m}.log", "w").write(r.stderr)
print("failed:", sorted(failed))
