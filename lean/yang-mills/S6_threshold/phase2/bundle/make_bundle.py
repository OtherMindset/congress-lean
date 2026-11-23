# Builds the posting payloads for the gate 2 bundle (S6 phase 2, run 1's evaluator), from the files in this folder.
# Writes bundle_payload.json (the three Lean files, "action": "bundle") and reference_program_payload.json
# (G_affine_reference_sc.py by code_ref). Standard library only.     python3 make_bundle.py
# Nothing is posted by this program. The operator posts, after a go.
import json, os, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, "..", "..", "..", "..", ".."))
TOOLCHAIN = "leanprover/lean4:v4.35.0"
MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"
NAME, MODEL, TABLE = "Claude council · Certifier", "claude-opus-5-5", "yang-mills"


def read(name):
    with open(os.path.join(HERE, name), encoding="utf-8") as f:
        return f.read()


ref_txt = open(os.path.join(REPO, "python", "yang-mills", "S6_threshold", "G_affine_reference.txt"), encoding="utf-8").read()
rows = [l for l in ref_txt.splitlines() if not l.startswith("#")]
assert len(rows) == 20
statements = [{"theorem": "GAff.ref%02d" % (i + 1),
               "claim": "For the box mu, r, d in [%s] x [%s] x [%s], the evaluator's affine form of G has the five "
                        "integers (c, a1, a2, a3, e) = (%s), as G_affine_reference.txt line %d."
                        % tuple([", ".join(r.split(" : ")[0].split()[2 * k:2 * k + 2]) for k in range(3)]
                                + [", ".join(r.split(" : ")[1].split()), i + 3])}
              for i, r in enumerate(rows)]
files = [
    {"module": "GAffineEval", "code": read("GAffineEval.lean"), "output": ""},
    {"module": "GAffineReference", "code": read("GAffineReference.lean"), "output": "", "statements": statements},
    {"module": "GAffineAll128", "code": read("GAffineAll128.lean"), "output": ""},
]
for f in files:
    assert len(f["code"]) <= 24000, f["module"]
bundle = {"table": TABLE, "action": "bundle", "name": NAME, "model": MODEL,
          "toolchain": TOOLCHAIN, "mathlib": MATHLIB, "files": files}
with open(os.path.join(HERE, "bundle_payload.json"), "w", encoding="utf-8") as f:
    json.dump(bundle, f, ensure_ascii=False, indent=1)
refprog = {"table": TABLE, "action": "post", "kind": "computation", "language": "python", "name": NAME, "model": MODEL,
           "code_ref": {"repo": "OtherMindset/congress-lean", "commit": "465adc6dfe85baa2c82a385347337a0cb0197fe8",
                        "path": "python/yang-mills/S6_threshold/G_affine_reference_sc.py",
                        "sha256": "06c610500e5d10e7bb4269cdbc76eb928dd62fe3fd1e7bf0ac6ec72372e26ef9"},
           "output": ref_txt.rstrip("\n")}
with open(os.path.join(HERE, "reference_program_payload.json"), "w", encoding="utf-8") as f:
    json.dump(refprog, f, ensure_ascii=False, indent=1)
for f in files:
    print(f["module"], len(f["code"]), hashlib.sha256(f["code"].encode("utf-8")).hexdigest())
print("statements", len(statements), "max claim", max(len(s["claim"]) for s in statements))
