# Builds the Lean files of phase 2 from GAffineEval.lean and the reference file.  Standard library only.
#   python3 make_lean.py ref        -> writes GAffineEvalRef.lean: the evaluator, then the 20 reference theorems
#   python3 make_lean.py all OUT    -> writes OUT: the evaluator, then `check b = true` for the 128 boxes
#                                      (local timing only; too long for one site post)
#   python3 make_lean.py one OUT    -> writes OUT: the evaluator, then `check b = true` for the reference box
#   python3 make_lean.py evalcheck OUT -> writes OUT: #eval comparison with the Python program on the 128 boxes
# The evaluator text is copied unchanged, so the prefix of every output is GAffineEval.lean byte for byte.
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
S6 = os.path.join(HERE, "..", "..", "..", "..", "python", "yang-mills", "S6_threshold")
EVAL = open(os.path.join(HERE, "GAffineEval.lean"), encoding="utf-8").read()


def box(fr):
    return "⟨" + ", ".join("%d, %d" % (f.numerator, f.denominator) for f in fr) + "⟩"


def reference():
    rows = []
    for ln in open(os.path.join(S6, "G_affine_reference.txt")).read().split("\n"):
        if ln and not ln.startswith("#"):
            b, v = ln.split(" : ")
            rows.append(([Fr(x) for x in b.split()], v.split()))
    assert len(rows) == 20
    return rows


def grid():
    # the grid of G_affine_cert.py: 8 x 8 x 2 boxes on [0, 4/5]^2 x [0, 1/5]
    em = [Fr(4, 5) * i / 8 for i in range(9)]
    ed = [Fr(1, 5) * i / 2 for i in range(3)]
    return [(em[i], em[i + 1], em[j], em[j + 1], ed[k], ed[k + 1])
            for i in range(8) for j in range(8) for k in range(2)]


def write(path, body):
    with open(path, "w", encoding="utf-8") as f:
        f.write(EVAL + body)


mode = sys.argv[1]
if mode == "ref":
    out = ["", "/-! ## Reference theorems (spec §3.3 item 1, checked on the site)", "",
           "For the 20 boxes of `python/yang-mills/S6_threshold/G_affine_reference.txt` (SHA-256 012e7361…), the",
           "five integers of the form of G, exactly as the Python program prints them. Box fields: μ lo, μ hi,",
           "r lo, r hi, d lo, d hi, each as numerator, denominator. -/", "namespace GAff", ""]
    for i, (fr, v) in enumerate(reference(), 1):
        out.append("theorem ref%02d : form %s =\n    (%s) := by decide +kernel" % (i, box(fr), ", ".join(v)))
    out += ["", "end GAff", ""]
    write(os.path.join(HERE, "GAffineEvalRef.lean"), "\n".join(out))
elif mode in ("all", "one"):
    bs = grid() if mode == "all" else [reference()[-1][0]]
    out = ["", "namespace GAff", ""]
    for i, b in enumerate(bs, 1):
        out.append("theorem box%03d : check %s = true := by decide +kernel" % (i, box(b)))
    out += ["", "end GAff", ""]
    write(sys.argv[2], "\n".join(out))
elif mode == "evalcheck":
    # local acceptance (no kernel): #eval compares, for all 128 boxes, the five integers of G, lo and hi of q
    # and of c, with the Python program's values, and requires check = true.  Imports the certificate.
    sys.path.insert(0, S6)
    import G_affine_cert as ga
    assert grid() == list(ga.boxes())
    rows = []
    for b in grid():
        g, q, c = ga.G_affine((b[0], b[1]), (b[2], b[3]), b[4], b[5])
        rows.append("(%s, (%d, %d, %d, %d, %d), (%d, %d), (%d, %d))" % (
            box(b), g.c, g.a1, g.a2, g.a3, g.e, q.lo(), q.hi(), c.lo(), c.hi()))
    out = ["", "namespace GAff", "def pyAll : List (Box × (Int × Int × Int × Int × Int) × (Int × Int) × (Int × Int)) := [",
           ",\n".join(rows), "]", "def lohi (x : AF) : Int × Int := (x.lo.toInt, x.hi.toInt)",
           "#eval pyAll.length",
           "#eval (pyAll.filter fun (b, g, q, c) => !(form b == g && lohi (evalBox b).q == q &&",
           "  lohi (evalBox b).c == c && check b)).length", "end GAff", ""]
    write(sys.argv[2], "\n".join(out))
else:
    raise SystemExit("mode: ref, all, one or evalcheck")
