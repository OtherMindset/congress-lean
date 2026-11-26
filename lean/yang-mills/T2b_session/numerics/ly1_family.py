"""One-parameter Lee-Yang family nu_s(dx) ∝ (x^2 + s) e^{-x^2/2} dx, s >= 0  (Z = e^{H^2/2}(1+s+H^2)/(1+s)).
LY: zeros H = ±i sqrt(1+s). Map sign of R'(H)."""
import mpmath as mp, numpy as np, json
from ly1 import cum_LP, Rp_from
mp.mp.dps = 40
out = []
for s in [0, 0.1, 0.3, 0.5, 1, 2, 3, 5, 10, 30]:
    a = mp.sqrt(1 + mp.mpf(s))
    vals = []
    for H in 10**np.linspace(-2, 1.3, 34):
        Rp, R, Pp = Rp_from(*cum_LP(mp.mpf('0.5'), [a], mp.mpf(H)))
        vals.append((float(H), float(Rp/Pp)))
    pos = [h for h, v in vals if v > 0]
    mx = max(vals, key=lambda t: t[1])
    out.append(dict(s=s, Hpos=[min(pos), max(pos)] if pos else None, max=mx))
    print("s=%5g  R'>0 for H in %s   max R'/P' = %.4g at H=%.3g" % (s, ("[%.3g, %.3g]" % (min(pos), max(pos))) if pos else "none", mx[1], mx[0]))
# GHS check: V = x^2/2 - log(x^2+s); V'' = 1 - 2(s - x^2)/(x^2+s)^2 ... nondecreasing on [0,inf)?
json.dump(out, open("ly1_family.json", "w"))
