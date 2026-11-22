# The proposed grid for phase 1: uniform 8 x 8 x 2 on [0, 4/5]^2 x [0, 1/5], cells 1/10 x 1/10 x 1/10.
# Writes grid_8x8x2.csv: exact cell ends and the float upper bound of G under three rule sets.
# python3 grid.py      PROTOTYPE (floats): the upper bounds are measurements, not certified values.
import sys, os
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import measure

NM, NR, ND = 8, 8, 2
E_MU = [Fr(4, 5) * i / NM for i in range(NM + 1)]
E_R = [Fr(4, 5) * j / NR for j in range(NR + 1)]
E_D = [Fr(1, 5) * k / ND for k in range(ND + 1)]
rows = [(E_MU[i], E_MU[i + 1], E_R[j], E_R[j + 1], E_D[k], E_D[k + 1])
        for i in range(NM) for j in range(NR) for k in range(ND)]
b = [np.array([float(rw[t]) for rw in rows]) for t in range(6)]
ub = {m: measure.ub(b, m)[0] for m in ("spec", "sq+best", "tight")}
with open(os.path.join(HERE, "grid_8x8x2.csv"), "w") as f:
    f.write("mu_lo,mu_hi,r_lo,r_hi,d_lo,d_hi,ub_spec,ub_sq_best,ub_tight\n")
    for n, rw in enumerate(rows):
        f.write(",".join(str(x) for x in rw) + ",%.6f,%.6f,%.6f\n" % (ub["spec"][n], ub["sq+best"][n], ub["tight"][n]))
for m, u in ub.items():
    print("rules %-8s: %d boxes, largest float upper bound %.5f, boxes above -0.005: %d" % (m, len(u), u.max(), int((u > -0.005).sum())))
