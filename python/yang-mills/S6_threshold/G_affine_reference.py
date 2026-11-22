# Reference file for the Lean evaluator (SPEC 2.5): for 20 fixed boxes, the five integers (c, a1, a2, a3, e)
# of the affine form of G computed by G_affine_cert.py at its P.     python3 G_affine_reference.py
# Writes G_affine_reference.txt.  Boxes: every 7th box of the grid (19 boxes) and the handoff's reference box.
import sys, os
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import G_affine_cert as ga

bx = list(ga.boxes())[::7] + [(Fr(400, 1000), Fr(405, 1000), Fr(40, 100), Fr(41, 100), Fr(126, 1000), Fr(154, 1000))]
assert len(bx) == 20
lines = ["# G_affine_cert.py, P = %d; values are integers scaled by 2^-%d" % (ga.P, ga.P),
         "# mu_lo mu_hi r_lo r_hi d_lo d_hi : c a1 a2 a3 e"]
for b in bx:
    g, q, c = ga.G_affine((b[0], b[1]), (b[2], b[3]), b[4], b[5])
    lines.append(" ".join(str(x) for x in b) + " : " + " ".join(str(v) for v in (g.c, g.a1, g.a2, g.a3, g.e)))
with open(os.path.join(HERE, "G_affine_reference.txt"), "w") as f:
    f.write("\n".join(lines) + "\n")
print("\n".join(lines))
