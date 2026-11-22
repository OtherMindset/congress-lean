# Float affine forms, vectorised over a batch of boxes.  PROTOTYPE: not rigorous, proves nothing.
#
#   x = c + a[0] eps_mu + a[1] eps_r + a[2] eps_d + [-E, E],   eps_i in [-1, 1],
#
# as in SPEC_small_certificate_and_kernel_checker.md, section 2.2.  Every field is a numpy array over the
# batch (c, E: shape (B,); a: shape (3, B)).  E is kept as a dict {source label: array} whose sum is the
# error term, so that the error of the final G can be split among the operations that created it
# (an exact linear split: see `mul`).  Float rounding is not modelled; the exact program rounds at 2^-104.
import numpy as np


class Ctx:
    B = 1                 # batch size
    stage = "misc"        # label of the evaluator stage, attached to every error created
    track = True          # keep one error entry per (operation, stage); else one entry in all
    prod = "spec"         # "spec": product rule of the spec, 2.2;  "sq": spec products, tight squares;
                          #  "tight": tight squares and diagonal terms of products (see mul() and sq())
    fn = "spec"           # "spec": alpha = lower bound of f' (spec 2.2);  "best": the endpoint derivative
                          #  (lower or upper bound of f') that gives the smaller spread;  "cheb": secant slope
    fails = {}            # guard name -> boolean array of boxes where it failed
    unit = 0.0            # if > 0: model the exact program's rounding by adding 4*unit to E at every
                          #  product, square, function rule and non-integer scaling (unit = 2^-P)


def _lab(op):
    return (op + "@" + Ctx.stage) if Ctx.track else "all"


def _merge(e1, e2):
    if not e1:
        return dict(e2)
    out = dict(e1)
    for k, v in e2.items():
        out[k] = out[k] + v if k in out else v
    return out


def _round(e):
    if Ctx.unit > 0:
        e = _merge(e, {"round@" + Ctx.stage if Ctx.track else "all": 4 * Ctx.unit + np.zeros(Ctx.B)})
    return e


def _scale(e, k):
    return {lab: v * k for lab, v in e.items()}


def _tot(e):
    s = 0.0
    for v in e.values():
        s = s + v
    return s


def fail(name, mask):
    m = Ctx.fails.get(name)
    Ctx.fails[name] = mask.copy() if m is None else (m | mask)


class AF:
    __slots__ = ("c", "a", "e")

    def __init__(s, c, a, e):
        s.c, s.a, s.e = c, a, e

    # construction
    @staticmethod
    def const(v):
        return AF(np.broadcast_to(np.asarray(v, float), (Ctx.B,)).copy(), np.zeros((3, Ctx.B)), {})

    @staticmethod
    def var(lo, hi, i):
        a = np.zeros((3, Ctx.B))
        a[i] = (hi - lo) / 2
        return AF((lo + hi) / 2, a, {})

    # summaries
    def lin(s):
        return np.abs(s.a).sum(0)

    def err(s):
        return _tot(s.e) + np.zeros(Ctx.B)

    def rad(s):
        return s.lin() + s.err()

    def lo(s):
        return s.c - s.rad()

    def hi(s):
        return s.c + s.rad()

    # linear operations: no new error
    def __add__(s, o):
        if not isinstance(o, AF):
            return AF(s.c + o, s.a, s.e)
        return AF(s.c + o.c, s.a + o.a, _merge(s.e, o.e))
    __radd__ = __add__

    def __neg__(s):
        return AF(-s.c, -s.a, s.e)

    def __sub__(s, o):
        return s + (-o)

    def __rsub__(s, o):
        return (-s) + o

    def __mul__(s, o):
        if isinstance(o, AF):
            return mul(s, o)
        e = _scale(s.e, np.abs(o))
        if not float(np.max(np.abs(o))).is_integer():
            e = _round(e)
        return AF(s.c * o, s.a * o, e)
    __rmul__ = __mul__

    def __truediv__(s, o):
        if isinstance(o, AF):
            return mul(s, recip(o))
        return s * (1.0 / o)

    def add_tail(s, tlo, thi, op="tail"):
        # the true value lies in x + [tlo, thi]: centre moves, half-width goes into E
        e = _merge(s.e, {_lab(op): (thi - tlo) / 2 + np.zeros(Ctx.B)})
        return AF(s.c + (tlo + thi) / 2, s.a, e)


def mul(x, y):
    # spec 2.2: centre x0 y0, linear x0 y_i + y0 x_i, new error (Lx+Ex)(Ly+Ey) + |x0|Ey + |y0|Ex.
    # Split exactly: Lx Ly is new (label mul@stage); Ex is scaled by (Ly + |y0| + Ey), Ey by (Lx + |x0|).
    # "tight": the diagonal terms x_i y_i eps_i^2 lie between 0 and x_i y_i, so the centre moves by
    #   sum x_i y_i / 2 and the new error is Lx Ly - sum |x_i y_i| / 2.
    if x is y:
        return sq(x)
    Lx, Ly = x.lin(), y.lin()
    Ex, Ey = x.err(), y.err()
    c = x.c * y.c
    a = x.c * y.a + y.c * x.a
    if Ctx.prod == "tight":
        dg = (x.a * y.a).sum(0)
        c = c + dg / 2
        new = Lx * Ly - np.abs(x.a * y.a).sum(0) / 2
    else:
        new = Lx * Ly
    e = _merge(_scale(x.e, Ly + np.abs(y.c) + Ey), _scale(y.e, Lx + np.abs(x.c)))
    e = _merge(e, {_lab("mul"): new})
    return AF(c, a, _round(e))


def sq(x):
    # "spec": the product rule with y = x.  "tight": (linear part + error)^2 lies in [0, R^2], R = Lx + Ex,
    #   so the centre moves by R^2/2 and R^2/2 + 2|x0|Ex is added (split: Lx^2/2 new, Ex scaled by Lx+Ex/2+2|x0|).
    Lx, Ex = x.lin(), x.err()
    if Ctx.prod == "spec":
        e = _merge(_scale(x.e, Lx + np.abs(x.c) + Ex), _scale(x.e, Lx + np.abs(x.c)))
        e = _merge(e, {_lab("mul"): Lx * Lx})
        return AF(x.c * x.c, 2 * x.c * x.a, _round(e))
    R = Lx + Ex
    e = _merge(_scale(x.e, Lx + Ex / 2 + 2 * np.abs(x.c)), {_lab("mul"): Lx * Lx / 2})
    return AF(x.c * x.c + R * R / 2, 2 * x.c * x.a, _round(e))


def _fnrule(x, name, f, dmin, dmax, xstar=None):
    # f(x) = alpha x + g(x); with alpha a lower (or upper) bound of f' on [lo, hi], g is monotone, so
    # g ranges over [g(lo), g(hi)] (spec 2.2).  "cheb": alpha = secant slope, then g has equal end values
    # and its other extreme at x* (f'(x*) = alpha); valid for convex or concave f only.
    lo, hi = x.lo(), x.hi()
    w = hi - lo
    flo, fhi = f(lo), f(hi)

    def spread(al):
        glo, ghi = flo - al * lo, fhi - al * hi
        return (glo + ghi) / 2, np.abs(ghi - glo) / 2

    if Ctx.fn == "cheb" and xstar is not None:
        al = np.where(w > 0, (fhi - flo) / np.where(w > 0, w, 1), dmin(lo, hi))
        xs = np.clip(xstar(al), lo, hi)
        gend, gmid = flo - al * lo, f(xs) - al * xs
        zeta, delta = (gend + gmid) / 2, np.abs(gend - gmid) / 2
    else:
        a1 = dmin(lo, hi)
        z1, d1 = spread(a1)
        if Ctx.fn == "spec":
            al, zeta, delta = a1, z1, d1
        else:
            a2 = dmax(lo, hi)
            z2, d2 = spread(a2)
            pick = d2 < d1
            al, zeta, delta = np.where(pick, a2, a1), np.where(pick, z2, z1), np.where(pick, d2, d1)
    e = _round(_merge(_scale(x.e, np.abs(al)), {_lab(name): delta}))
    return AF(al * x.c + zeta, al * x.a, e)


def recip(x):
    lo, hi = x.lo(), x.hi()
    neg = hi < 0
    bad = ~((lo > 0) | neg)
    if bad.any():
        fail("recip: range contains 0", bad)
    if neg.all():
        return -recip(-x)
    if neg.any():
        raise NotImplementedError("mixed signs in a batch")
    with np.errstate(all="ignore"):
        return _fnrule(x, "recip", lambda v: 1 / v,
                       lambda l, h: -1 / (l * l), lambda l, h: -1 / (h * h),
                       lambda al: 1 / np.sqrt(-al))


def sqrt(x):
    bad = x.lo() <= 0
    if bad.any():
        fail("sqrt: range not > 0", bad)
    with np.errstate(all="ignore"):
        return _fnrule(x, "sqrt", np.sqrt,
                       lambda l, h: 0.5 / np.sqrt(h), lambda l, h: 0.5 / np.sqrt(l),
                       lambda al: 1 / (4 * al * al))


def exp(x):
    with np.errstate(all="ignore"):
        return _fnrule(x, "exp", np.exp, lambda l, h: np.exp(l), lambda l, h: np.exp(h), np.log)


def asin(x):
    lo, hi = x.lo(), x.hi()
    bad = (lo <= -1) | (hi >= 1)
    if bad.any():
        fail("asin: range not in (-1,1)", bad)

    def dp(v):
        return 1 / np.sqrt(1 - v * v)

    def dmin(l, h):  # f' is even and increasing in |v|
        m = np.where((l <= 0) & (h >= 0), 0.0, np.minimum(np.abs(l), np.abs(h)))
        return dp(m)

    def dmax(l, h):
        return dp(np.maximum(np.abs(l), np.abs(h)))
    with np.errstate(all="ignore"):
        return _fnrule(x, "asin", np.arcsin, dmin, dmax, None)
