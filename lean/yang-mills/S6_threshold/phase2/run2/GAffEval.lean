/-!
# S6 phase 2: `Eval` for the affine-form certificate (one box)

A port of `python/yang-mills/S6_threshold/G_affine_cert.py` at commit 95d0843 to Lean 4, core only
(no Mathlib), for Lean's kernel: `check b = true` is meant to be proved by `decide +kernel`.
Same algorithm, same rounding, P = 64: `gform b` gives the same five integers (c, a1, a2, a3, e) as
`G_affine` in the Python program. No soundness proof here (that is phase 3). Lattice only.

Fragment: natural numbers only. A signed integer is a sign and a magnitude (`Z`); a rational is a
signed numerator over a positive natural denominator (`Q`), never reduced: only floors, ceilings
and comparisons of rationals are used, and those do not depend on the representation. Rounding at
2^-64 is a shift. Comparisons are `Nat.ble` / `Nat.beq`. No type-class arithmetic in the evaluator.
Tables (moments, series) are lists walked from the front, never indexed.

Guards: every `need(...)` of the Python program becomes a Boolean carried in the `ok` field of the
form it guards, and `ok` is the conjunction over all inputs of an operation. So `(gform b).ok` is
true only if every guard held. Some guards are additions; they only make `check` stricter. The box
must have lo ≤ hi with positive denominators (for lo > hi the integers differ from Python's, and
`ok` is false). Each integer square root is checked (r*r ≤ n < (r+1)*(r+1)). The two tails built
from cosh must have a nonnegative numerator, and `pairs` must produce three entries; these last
two cannot fail. A `Box` has natural-number endpoints, so the claim of equal integers is for boxes
with nonnegative rational endpoints.
-/
namespace GAff

/-! ## Constants -/

def P : Nat := 64
def S : Nat := Nat.shiftLeft 1 64
def S2 : Nat := Nat.mul S S
def S3 : Nat := Nat.mul S2 S

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.mul (n + 1) (fact n)

/-- ceil (a / n), for n > 0 -/
def cdivN (a n : Nat) : Nat := Nat.div (Nat.add a (Nat.sub n 1)) n
/-- ceil (a / 2^P) -/
def cdivP (a : Nat) : Nat := Nat.shiftRight (Nat.add a (Nat.sub S 1)) P
def nlt (a b : Nat) : Bool := Nat.ble (Nat.add a 1) b
def nmin (a b : Nat) : Nat := bif Nat.ble a b then a else b
def nmax (a b : Nat) : Nat := bif Nat.ble a b then b else a

/-! ## Signed integers: sign (true = negative) and magnitude. -0 is allowed; every
function below depends only on the value. -/

structure Z where
  neg : Bool
  mag : Nat

def zof (n : Nat) : Z := ⟨false, n⟩
def zneg (x : Z) : Z := ⟨!x.neg, x.mag⟩
/-- a - b for naturals a, b -/
def zsubN (a b : Nat) : Z := bif Nat.ble b a then ⟨false, Nat.sub a b⟩ else ⟨true, Nat.sub b a⟩
def zadd : Z → Z → Z
  | ⟨false, a⟩, ⟨false, b⟩ => ⟨false, Nat.add a b⟩
  | ⟨true, a⟩, ⟨true, b⟩ => ⟨true, Nat.add a b⟩
  | ⟨false, a⟩, ⟨true, b⟩ => zsubN a b
  | ⟨true, a⟩, ⟨false, b⟩ => zsubN b a
def zsub (x y : Z) : Z := zadd x (zneg y)
def zmul : Z → Z → Z
  | ⟨false, a⟩, ⟨false, b⟩ => ⟨false, Nat.mul a b⟩
  | ⟨true, a⟩, ⟨true, b⟩ => ⟨false, Nat.mul a b⟩
  | ⟨false, a⟩, ⟨true, b⟩ => ⟨true, Nat.mul a b⟩
  | ⟨true, a⟩, ⟨false, b⟩ => ⟨true, Nat.mul a b⟩
def zmulN (x : Z) (k : Nat) : Z := ⟨x.neg, Nat.mul x.mag k⟩
/-- floor (x / 2^p) (Python `x >> p`) -/
def zshr (x : Z) (p : Nat) : Z :=
  bif x.neg then ⟨true, Nat.shiftRight (Nat.add x.mag (Nat.sub (Nat.shiftLeft 1 p) 1)) p⟩
  else ⟨false, Nat.shiftRight x.mag p⟩
/-- floor (x / n), n > 0 (Python `x // n`) -/
def zfdiv (x : Z) (n : Nat) : Z :=
  bif x.neg then ⟨true, cdivN x.mag n⟩ else ⟨false, Nat.div x.mag n⟩
/-- x < y -/
def zlt : Z → Z → Bool
  | ⟨false, a⟩, ⟨false, b⟩ => nlt a b
  | ⟨true, a⟩, ⟨true, b⟩ => nlt b a
  | ⟨false, _⟩, ⟨true, _⟩ => false
  | ⟨true, a⟩, ⟨false, b⟩ => nlt 0 (Nat.add a b)
def zle (x y : Z) : Bool := !(zlt y x)
def zpos (x : Z) : Nat := bif x.neg then 0 else x.mag   -- max(x, 0)

/-! ## Rationals n / d, d > 0, unreduced -/

structure Q where
  n : Z
  d : Nat

def qlt (a b : Q) : Bool := zlt (zmulN a.n b.d) (zmulN b.n a.d)
def qmin (a b : Q) : Q := bif qlt b a then b else a
def qmax (a b : Q) : Q := bif qlt a b then b else a
def qadd (a b : Q) : Q := ⟨zadd (zmulN a.n b.d) (zmulN b.n a.d), Nat.mul a.d b.d⟩
def qsub (a b : Q) : Q := qadd a ⟨zneg b.n, b.d⟩
def qmul (a b : Q) : Q := ⟨zmul a.n b.n, Nat.mul a.d b.d⟩
def qhalf (a : Q) : Q := ⟨a.n, Nat.mul 2 a.d⟩
def qfloor (a : Q) : Z := zfdiv a.n a.d
def qceil (a : Q) : Z := zneg (zfdiv (zneg a.n) a.d)
def qscale (a : Q) : Q := ⟨zmulN a.n S, a.d⟩   -- S * a

/-! ## Affine forms (c, a1, a2, a3, e) at scale 2^-P, with the guard flag -/

structure A where
  c : Z
  a1 : Z
  a2 : Z
  a3 : Z
  e : Nat
  ok : Bool

def AL (x : A) : Nat := Nat.add (Nat.add x.a1.mag x.a2.mag) x.a3.mag
def AR (x : A) : Nat := Nat.add (AL x) x.e
def alo (x : A) : Z := zsub x.c (zof (AR x))
def ahi (x : A) : Z := zadd x.c (zof (AR x))
/-- cv(k) for a natural k: (k * 2^P, 0, 0, 0, 0) -/
def aint (k : Nat) : A := ⟨zof (Nat.shiftLeft k P), zof 0, zof 0, zof 0, 0, true⟩
def azero : A := aint 0
def aguard (x : A) (b : Bool) : A := { x with ok := x.ok && b }
def aadd (x y : A) : A :=
  ⟨zadd x.c y.c, zadd x.a1 y.a1, zadd x.a2 y.a2, zadd x.a3 y.a3, Nat.add x.e y.e, x.ok && y.ok⟩
def aneg (x : A) : A := ⟨zneg x.c, zneg x.a1, zneg x.a2, zneg x.a3, x.e, x.ok⟩
def asub (x y : A) : A := aadd x (aneg y)
/-- x * k for a natural k (exact) -/
def amulN (x : A) (k : Nat) : A :=
  ⟨zmulN x.c k, zmulN x.a1 k, zmulN x.a2 k, zmulN x.a3 k, Nat.mul x.e k, x.ok⟩
/-- product rule (MUL) -/
def amul (x y : A) : A :=
  let num := Nat.add (Nat.add (Nat.mul x.c.mag y.e) (Nat.mul y.c.mag x.e)) (Nat.mul (AR x) (AR y))
  ⟨zshr (zmul x.c y.c) P,
   zshr (zadd (zmul x.c y.a1) (zmul y.c x.a1)) P,
   zshr (zadd (zmul x.c y.a2) (zmul y.c x.a2)) P,
   zshr (zadd (zmul x.c y.a3) (zmul y.c x.a3)) P,
   Nat.add (cdivP num) 4, x.ok && y.ok⟩
/-- square rule (SQ) -/
def asq (x : A) : A :=
  let R := AR x
  let cm := x.c.mag
  let t := Nat.shiftLeft 1 (Nat.add P 1)
  ⟨zof (Nat.div (Nat.add (Nat.mul 2 (Nat.mul cm cm)) (Nat.mul R R)) t),
   zshr (zmul x.c x.a1) (Nat.sub P 1),
   zshr (zmul x.c x.a2) (Nat.sub P 1),
   zshr (zmul x.c x.a3) (Nat.sub P 1),
   Nat.add (cdivN (Nat.add (Nat.mul R R) (Nat.mul 4 (Nat.mul cm x.e))) t) 4, x.ok⟩
/-- x / n for a natural n > 0 -/
def adivN (x : A) (n : Nat) : A :=
  ⟨zfdiv x.c n, zfdiv x.a1 n, zfdiv x.a2 n, zfdiv x.a3 n, Nat.add (cdivN x.e n) 4,
   x.ok && nlt 0 n⟩
def awiden (x : A) (t : Nat) : A := { x with e := Nat.add x.e t }

/-! ## Integer square root (Newton from above), checked -/

def isqrtIter : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | f + 1, n, x =>
    let y := Nat.shiftRight (Nat.add x (Nat.div n x)) 1
    bif nlt y x then isqrtIter f n y else x
def isqrt (n : Nat) : Nat :=
  bif Nat.beq n 0 then 0
  else isqrtIter 200 n (Nat.shiftLeft 1 (Nat.add (Nat.shiftRight (Nat.log2 n) 1) 1))
def isqrtOK (n r : Nat) : Bool :=
  Nat.ble (Nat.mul r r) n && nlt n (Nat.mul (Nat.add r 1) (Nat.add r 1))
/-- ceil (sqrt n) from r = isqrt n -/
def csq (n r : Nat) : Nat := bif Nat.beq (Nat.mul r r) n then r else Nat.add r 1

/-! ## Enclosures of exp and asin at rationals (exp_iv, cosh_hi, asin_iv) -/

/-- sum over j = 0..40 of m^j d^(40-j) 40!/j!, split by sign (odd j negative if `sg`).
Called with j = 40, c = 1; c is 40!/j! -/
def expLoop (m d : Nat) (sg : Bool) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, c, p, q => (Nat.add p (Nat.mul (Nat.pow d 40) c), q)
  | j + 1, c, p, q =>
    let t := Nat.mul (Nat.mul (Nat.pow m (Nat.add j 1)) (Nat.pow d (Nat.sub 39 j))) c
    bif sg && Nat.beq (Nat.mod (Nat.add j 1) 2) 1 then expLoop m d sg j (Nat.mul c (Nat.add j 1)) p (Nat.add q t)
    else expLoop m d sg j (Nat.mul c (Nat.add j 1)) (Nat.add p t) q

/-- exp_iv (n/d) = (s - EXP_R, s + EXP_R), s = sum_{j <= 40} q^j/j!, EXP_R = 2^44/41!;
with the guard |n/d| <= 2 -/
def expIv (n : Z) (d : Nat) : Q × Q × Bool :=
  let pq := expLoop n.mag d n.neg 40 1 0 0
  let num := zmulN (zsubN pq.1 pq.2) 41
  let dd := Nat.pow d 40
  let E := zof (Nat.mul (Nat.pow 2 44) dd)
  let den := Nat.mul dd (fact 41)
  (⟨zsub num E, den⟩, ⟨zadd num E, den⟩, Nat.ble n.mag (Nat.mul 2 d) && nlt 0 d)

/-- cosh_hi (h/d) = (exp_iv(h/d).hi + exp_iv(-h/d).hi) / 2 -/
def coshHi (h d : Nat) : Q × Bool :=
  let a := expIv (zof h) d
  let b := expIv ⟨true, h⟩ d
  (qhalf (qadd a.2.1 b.2.1), a.2.2 && b.2.2)

/-- 61!! = 1 * 3 * ... * 61, and M = 4^30 * 61!! -/
def ODD : Nat := Nat.div (fact 61) (Nat.mul (Nat.pow 2 30) (fact 30))
def AM : Nat := Nat.mul (Nat.pow 4 30) ODD

/-- sum over k = 0..30 of (M * C_k) u^(2k+1) S^(60-2k), C_k = (2k)!/(4^k k!^2 (2k+1)).
Called with fuel 31, k = 0, f2 = (2k)! = 1, f1 = k! = 1 -/
def asinLoop (u : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | f + 1, k, f2, f1, acc =>
    let ck := Nat.div (Nat.mul f2 AM)
      (Nat.mul (Nat.mul (Nat.pow 4 k) (Nat.mul f1 f1)) (Nat.add (Nat.mul 2 k) 1))
    let t := Nat.mul (Nat.mul ck (Nat.pow u (Nat.add (Nat.mul 2 k) 1))) (Nat.pow S (Nat.sub 60 (Nat.mul 2 k)))
    asinLoop u f (Nat.add k 1)
      (Nat.mul f2 (Nat.mul (Nat.add (Nat.mul 2 k) 1) (Nat.add (Nat.mul 2 k) 2)))
      (Nat.mul f1 (Nat.add k 1)) (Nat.add acc t)

/-- asin_iv (u/S) for u >= 0: (s, s + q^63/(1 - q^2)) -/
def asinIvPos (u : Nat) : Q × Q :=
  let sN := asinLoop u 31 0 1 1 0
  let den := Nat.mul AM (Nat.pow S 61)
  let w := Nat.sub S2 (Nat.mul u u)
  (⟨zof sN, den⟩, ⟨zof (Nat.add (Nat.mul sN w) (Nat.mul AM (Nat.pow u 63))), Nat.mul den w⟩)

/-- asin_iv (v/S), odd extension; the guard |v/S| <= 1/4 -/
def asinIv (v : Z) : Q × Q × Bool :=
  let r := asinIvPos v.mag
  let g := Nat.ble (Nat.mul 4 v.mag) S
  bif v.neg then (⟨zneg r.2.n, r.2.d⟩, ⟨zneg r.1.n, r.1.d⟩, g) else (r.1, r.2, g)

/-! ## The function rule (FN) and 1/x, sqrt, exp, asin -/

/-- f - al * v / S, in units of 2^-P -/
def gsub (f : Q) (al v : Z) : Q := ⟨zsub (zmulN f.n S) (zmulN (zmul al v) f.d), Nat.mul f.d S⟩
def hull4 (a b c d : Q) : Q × Q := (qmin (qmin (qmin a b) c) d, qmax (qmax (qmax a b) c) d)

/-- fn_rule: f(lo), f(hi) enclosed by [f0l, f0h], [f1l, f1h] (in units), slopes al1, al2 -/
def fnRule (x : A) (lo hi : Z) (f0l f0h f1l f1h : Q) (al1 al2 : Z) : A :=
  let b1 := hull4 (gsub f0l al1 lo) (gsub f0h al1 lo) (gsub f1l al1 hi) (gsub f1h al1 hi)
  let b2 := hull4 (gsub f0l al2 lo) (gsub f0h al2 lo) (gsub f1l al2 hi) (gsub f1h al2 hi)
  let pick := qlt (qsub b2.2 b2.1) (qsub b1.2 b1.1)
  let al := bif pick then al2 else al1
  let gl := bif pick then b2.1 else b1.1
  let gh := bif pick then b2.2 else b1.2
  let zeta := qfloor (qhalf (qadd gl gh))
  let delta := Nat.add (qceil (qhalf (qsub gh gl))).mag 1
  let y := amul x ⟨al, zof 0, zof 0, zof 0, 0, true⟩
  ⟨zadd y.c zeta, y.a1, y.a2, y.a3, Nat.add y.e delta, y.ok⟩

/-- 1/x for x with lo > 0 -/
def recipPos (x : A) : A :=
  let lo := alo x
  let hi := ahi x
  let l := lo.mag
  let h := hi.mag
  let f0 : Q := ⟨zof S2, l⟩
  let f1 : Q := ⟨zof S2, h⟩
  aguard (fnRule x lo hi f0 f0 f1 f1 ⟨true, cdivN S3 (Nat.mul l l)⟩ ⟨true, Nat.div S3 (Nat.mul h h)⟩)
    (zlt (zof 0) lo)
def arecip (x : A) : A := bif zlt (ahi x) (zof 0) then aneg (recipPos (aneg x)) else recipPos x

def asqrt (x : A) : A :=
  let lo := alo x
  let hi := ahi x
  let nl := Nat.mul lo.mag S
  let nh := Nat.mul hi.mag S
  let rl := isqrt nl
  let rh0 := isqrt nh
  let rh := csq nh rh0
  aguard (fnRule x lo hi ⟨zof rl, 1⟩ ⟨zof (csq nl rl), 1⟩ ⟨zof rh0, 1⟩ ⟨zof rh, 1⟩
      (zof (Nat.div S2 (Nat.mul 2 rh))) (zof (cdivN S2 (Nat.mul 2 rl))))
    (zlt (zof 0) lo && nlt 0 rl && isqrtOK nl rl && isqrtOK nh rh0)

def aexp (x : A) : A :=
  let lo := alo x
  let hi := ahi x
  let e0 := expIv lo S
  let e1 := expIv hi S
  aguard (fnRule x lo hi (qscale e0.1) (qscale e0.2.1) (qscale e1.1) (qscale e1.2.1)
      (qfloor (qscale e0.1)) (qceil (qscale e1.2.1)))
    (e0.2.2 && e1.2.2)

def aasin (x : A) : A :=
  let lo := alo x
  let hi := ahi x
  let f0 := asinIv lo
  let f1 := asinIv hi
  let m := bif zle lo (zof 0) && zle (zof 0) hi then 0 else nmin lo.mag hi.mag
  let M := nmax lo.mag hi.mag
  let ym := Nat.sub S2 (Nat.mul m m)
  let yM := Nat.sub S2 (Nat.mul M M)
  let sm0 := isqrt ym
  let sM := isqrt yM
  aguard (fnRule x lo hi (qscale f0.1) (qscale f0.2.1) (qscale f1.1) (qscale f1.2.1)
      (zof (Nat.div S2 (csq ym sm0))) (zof (cdivN S2 sM)))
    (zle (zneg (zof (Nat.div S 4))) lo && zle hi (zof (Nat.div S 4)) && f0.2.2 && f1.2.2
      && nlt 0 sM && isqrtOK ym sm0 && isqrtOK yM sM)

/-! ## pi (Machin), the full-range table moments, pi/4 -/

/-- sum over k = 0..n of (-1)^k b^(2(n-k)) O/(2k+1), split by sign; O = (2n+1)!! -/
def atanLoop (b n O : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, p, q => (p, q)
  | f + 1, k, p, q =>
    let t := Nat.mul (Nat.pow b (Nat.mul 2 (Nat.sub n k))) (Nat.div O (Nat.add (Nat.mul 2 k) 1))
    bif Nat.beq (Nat.mod k 2) 1 then atanLoop b n O f (Nat.add k 1) p (Nat.add q t)
    else atanLoop b n O f (Nat.add k 1) (Nat.add p t) q
def oddf (n : Nat) : Nat := Nat.div (fact (Nat.add (Nat.mul 2 n) 1)) (Nat.mul (Nat.pow 2 n) (fact n))
/-- numerator of atan_fr(1/b, n)'s last partial sum s_n over b^(2n+1) (2n+1)!! -/
def atanN (b n : Nat) : Nat := let pq := atanLoop b n (oddf n) (Nat.add n 1) 0 0 0; Nat.sub pq.1 pq.2
def O40 : Nat := oddf 40
def O20 : Nat := oddf 20
def D5 : Nat := Nat.mul (Nat.pow 5 81) O40
def D239 : Nat := Nat.mul (Nat.pow 239 41) O20
def N40 : Nat := atanN 5 40
def N20 : Nat := atanN 239 20
/-- PI_LO = 16 s39(1/5) - 4 s20(1/239), PI_HI = 16 s40(1/5) - 4 s19(1/239);
PS = PI_LO + PI_HI and PD = PI_HI - PI_LO, over PDEN -/
def PDEN : Nat := Nat.mul D5 D239
def PS : Nat :=
  Nat.sub (Nat.mul 16 (Nat.mul (Nat.sub (Nat.mul 2 N40) (Nat.div O40 81)) D239))
    (Nat.mul 4 (Nat.mul (Nat.sub (Nat.mul 2 N20) (Nat.div O20 41)) D5))
def PD : Nat := Nat.add (Nat.mul 16 (Nat.mul (Nat.div O40 81) D239)) (Nat.mul 4 (Nat.mul (Nat.div O20 41) D5))

/-- const(lo, hi): centre floor(S * mid), e = ceil(S * half-width) + 1 -/
def aconst (mid hw : Q) : A :=
  ⟨qfloor (qscale mid), zof 0, zof 0, zof 0, Nat.add (qceil (qscale hw)).mag 1, true⟩
/-- PI4 = const(PI_LO/4, PI_HI/4) -/
def PI4 : A := aconst ⟨zof PS, Nat.mul 8 PDEN⟩ ⟨zof PD, Nat.mul 8 PDEN⟩

/-- QFULL row 0 times QD = 2^24 * 24!: base[0] = 1/2, base[1] = 0, base[n] = base[n-2] (n-1)/(n+2) -/
def QD : Nat := Nat.mul (Nat.pow 2 24) (fact 24)
def qbase : Nat → Nat → Nat → Nat → List Z
  | 0, _, _, _ => []
  | f + 1, n, b2, b1 =>
    let bn := Nat.div (Nat.mul b2 (Nat.sub n 1)) (Nat.add n 2)
    zof bn :: qbase f (Nat.add n 1) b1 bn
def QROW0 : List Z := zof (Nat.div QD 2) :: zof 0 :: qbase 45 2 (Nat.div QD 2) 0
def zdiff : List Z → List Z
  | a :: b :: c :: t => zsub a c :: zdiff (b :: c :: t)
  | _ => []
/-- FULLC[k][n] = const(sorted(q PI_LO/(2k+1)!, q PI_HI/(2k+1)!)), q = QFULL[k][n] = qn/QD -/
def fullc (k : Nat) (qn : Z) : A :=
  let den := Nat.mul (Nat.mul 2 (fact (Nat.add (Nat.mul 2 k) 1))) (Nat.mul QD PDEN)
  aconst ⟨zmulN qn PS, den⟩ ⟨zof (Nat.mul qn.mag PD), den⟩

/-! ## Lists of forms, walked from the front -/

def zipAdd (f : A → A) : List A → List A → List A
  | a :: as, t :: ts => aadd a (f t) :: zipAdd f as ts
  | _, _ => []
def zeros : Nat → List A
  | 0 => []
  | n + 1 => azero :: zeros n
def adiff : List A → List A
  | a :: b :: c :: t => asub a c :: adiff (b :: c :: t)
  | _ => []
def drop2 : List A → List A
  | _ :: _ :: t => t
  | _ => []
def tl1 : List A → List A
  | _ :: t => t
  | [] => []
/-- [cv 1, cv 1 * x, (cv 1 * x) * x, ...], n + 1 entries -/
def powersAux (x : A) : Nat → A → List A
  | 0, p => [p]
  | n + 1, p => p :: powersAux x n (amul p x)
def powers (x : A) (n : Nat) : List A := powersAux x n (aint 1)

/-- rsum_full: G[n] = sum_k rp[k] FULLC[k][n], n <= 31 -/
def rsumFullAux : List A → Nat → List Z → List A → List A
  | [], _, _, acc => acc
  | r :: rs, k, qrow, acc =>
    rsumFullAux rs (Nat.add k 1) (zdiff qrow) (zipAdd (fun t => amul r t) acc (qrow.map (fullc k)))
def rsumFull (rp : List A) : List A := rsumFullAux rp 0 QROW0 (zeros 32)

/-- rsum: G[n] = sum_k (rp[k] tab[k][n]) / (2k+1)!, tab = ktab(base) -/
def rsumAux : List A → Nat → List A → List A → List A
  | [], _, _, acc => acc
  | r :: rs, k, row, acc =>
    rsumAux rs (Nat.add k 1) (adiff row)
      (zipAdd (fun t => adivN (amul r t) (fact (Nat.add (Nat.mul 2 k) 1))) acc row)
def rsum (rp base : List A) : List A := rsumAux rp 0 base (zeros 32)

/-- mhat: Mh[k] = sum_{i <= 18} (mp[i] G[k+i]) / i!, k <= 13 -/
def mhatAux : List A → Nat → List A → List A → List A
  | [], _, _, acc => acc
  | m :: ms, i, g, acc => mhatAux ms (Nat.add i 1) (tl1 g) (zipAdd (fun t => adivN (amul m t) (fact i)) acc g)
def mhat (G mp : List A) : List A := mhatAux mp 0 G (zeros 14)

/-- pairs: E_n = sum_j (dp[j] Mh[n+2j])/(2j)!, O_n = sum_j (dp[j] Mh[n+2j+1])/(2j+1)!, n <= 2 -/
def pairsAux : List A → Nat → List A → List A → List A → List A → List A × List A
  | [], _, _, _, ea, oa => (ea, oa)
  | p :: ps, j, ev, od, ea, oa =>
    pairsAux ps (Nat.add j 1) (drop2 ev) (drop2 od)
      (zipAdd (fun t => adivN (amul p t) (fact (Nat.mul 2 j))) ea ev)
      (zipAdd (fun t => adivN (amul p t) (fact (Nat.add (Nat.mul 2 j) 1))) oa od)

structure P3 where
  e0 : A
  o0 : A
  e1 : A
  o1 : A
  e2 : A
  o2 : A

def get3 (l : List A) (t : Nat) : A × A × A :=
  match l with
  | [a, b, c] => (awiden a t, awiden b t, awiden c t)
  | _ => (aguard azero false, aguard azero false, aguard azero false)
def pairs (Mh dp : List A) (t : Nat) : P3 :=
  let r := pairsAux dp 0 Mh (tl1 Mh) (zeros 3) (zeros 3)
  let e := get3 r.1 t
  let o := get3 r.2 t
  ⟨e.1, o.1, e.2.1, o.2.1, e.2.2, o.2.2⟩

/-! ## inc_table, phi, the atanh series -/

/-- base[n] for n >= 2: (base[n-2] (n-1) + c^(n-1) w3) / (n+2); cp = c^(n-1) as computed in
Python (cp * c, which is sq(c) at n = 2, where cp is c itself) -/
def incBase (w3 c : A) : Nat → Nat → A → A → A → List A
  | 0, _, _, _, _ => []
  | f + 1, n, b2, b1, cp =>
    let bn := adivN (aadd (amulN b2 (Nat.sub n 1)) (amul cp w3)) (Nat.add n 2)
    bn :: incBase w3 c f (Nat.add n 1) b1 bn (bif Nat.beq n 2 then asq c else amul cp c)
def incRow0 (c w : A) : List A :=
  let w3 := amul (asq w) w
  let b0 := asub PI4 (adivN (aadd (amul c w) (aasin c)) 2)
  let b1 := adivN w3 3
  b0 :: b1 :: incBase w3 c 45 2 b0 b1 c

/-- s = sum_{k <= 7} p_k/(2k+1)!, p_0 = cv 1, p_{k+1} = p_k * z2 -/
def phiLoop (z2 : A) : Nat → Nat → A → A → A
  | 0, _, _, s => s
  | f + 1, k, p, s => phiLoop z2 f (Nat.add k 1) (amul p z2) (aadd s (adivN p (fact (Nat.add (Nat.mul 2 k) 1))))
def aphi (z : A) : A :=
  let z2 := asq z
  let s := phiLoop z2 8 0 (aint 1) azero
  let H := zpos (ahi z)
  let H2 := zpos (ahi z2)
  let ch := coshHi H S
  -- ceil(S * (H2/S)^8 * cosh_hi(H/S) / 17!)
  let t := cdivN (Nat.mul (Nat.pow H2 8) ch.1.n.mag) (Nat.mul (Nat.mul (Nat.pow S 7) ch.1.d) (fact 17))
  aguard (awiden s t) (ch.2 && !ch.1.n.neg)

/-- a = sum_{k <= 12} u2^k/(2k+1) -/
def atanhLoop (u2 : A) : Nat → Nat → A → A → A
  | 0, _, _, a => a
  | f + 1, k, p, a => atanhLoop u2 f (Nat.add k 1) (amul p u2) (aadd a (adivN p (Nat.add (Nat.mul 2 k) 1)))

/-! ## One box -/

/-- a box: mu in [mln/mld, mhn/mhd], r in [rln/rld, rhn/rhd], d in [dln/dld, dhn/dhd] -/
structure Box where
  mln : Nat
  mld : Nat
  mhn : Nat
  mhd : Nat
  rln : Nat
  rld : Nat
  rhn : Nat
  rhd : Nat
  dln : Nat
  dld : Nat
  dhn : Nat
  dhd : Nat

/-- var(lo, hi, i): centre floor(S (lo+hi)/2), coefficient ceil(S (hi-lo)/2) + 1 in slot i -/
def avar (ln ld hn hd : Nat) (i : Nat) : A :=
  let den := Nat.mul 2 (Nat.mul ld hd)
  let cm := Nat.div (Nat.mul (Nat.add (Nat.mul ln hd) (Nat.mul hn ld)) S) den
  let a := zof (Nat.add (cdivN (Nat.mul (Nat.sub (Nat.mul hn ld) (Nat.mul ln hd)) S) den) 1)
  let g := Nat.ble (Nat.mul ln hd) (Nat.mul hn ld) && nlt 0 ld && nlt 0 hd
  match i with
  | 0 => ⟨zof cm, a, zof 0, zof 0, 0, g⟩
  | 1 => ⟨zof cm, zof 0, a, zof 0, 0, g⟩
  | _ => ⟨zof cm, zof 0, zof 0, a, 0, g⟩

/-- the series tail, ceil(S * 2 e^muh cosh(dh) cosh(rh) (dh^12/12! + muh^19/19! + rh^16/17!)),
with exp and cosh by exp_iv's upper ends -/
def tailG (b : Box) : Nat × Bool :=
  let em := expIv (zof b.mhn) b.mhd
  let cd := coshHi b.dhn b.dhd
  let cr := coshHi b.rhn b.rhd
  let s := qadd (qadd ⟨zof (Nat.pow b.dhn 12), Nat.mul (Nat.pow b.dhd 12) (fact 12)⟩
      ⟨zof (Nat.pow b.mhn 19), Nat.mul (Nat.pow b.mhd 19) (fact 19)⟩)
      ⟨zof (Nat.pow b.rhn 16), Nat.mul (Nat.pow b.rhd 16) (fact 17)⟩
  let T := qmul (qmul (qmul (qmul ⟨zof 2, 1⟩ em.2.1) cd.1) cr.1) s
  (cdivN (Nat.mul T.n.mag S) T.d, em.2.2 && cd.2 && cr.2 && !T.n.neg)

/-- pair products: (x0 y0 + d2 x1 y1, x0 y1 + x1 y0); `psq` is the case x = y (Python's
`o is s`, which uses the square rule for x0 x0 and x1 x1) -/
def pmul (d2 : A) (x y : A × A) : A × A :=
  (aadd (amul x.1 y.1) (amul d2 (amul x.2 y.2)), aadd (amul x.1 y.2) (amul x.2 y.1))
def psq (d2 : A) (x : A × A) : A × A :=
  (aadd (asq x.1) (amul d2 (asq x.2)), aadd (amul x.1 x.2) (amul x.2 x.1))
def pmul2 (x y : A × A) : A := aadd (amul x.1 y.2) (amul x.2 y.1)

/-- G_affine: the affine form of G over the box -/
def gform (b : Box) : A :=
  let m := avar b.mln b.mld b.mhn b.mhd 0
  let rr := avar b.rln b.rld b.rhn b.rhd 1
  let dv := avar b.dln b.dld b.dhn b.dhd 2
  let d2 := asq dv
  let r2 := asq rr
  let tl := tailG b
  let rp := powers r2 7
  let mp := powers m 18
  let dp := powers d2 5
  let Zp := pairs (mhat (rsumFull rp) mp) dp tl.1
  let t := amul Zp.o0 (arecip Zp.e0)
  let u2 := amul d2 (asq t)
  let H := zpos (ahi u2)
  let a := awiden (atanhLoop u2 13 0 (aint 1) azero) (cdivN (Nat.mul 2 (Nat.pow H 13)) (Nat.pow S 12))
  let c0 := amul t a
  let c := aguard c0 (tl.2 && zlt (ahi u2) (zof (Nat.div S 4))
    && zle (zneg (zof (Nat.div S 64))) (alo c0) && zle (ahi c0) (zof (Nat.div S 4)))
  let w := asqrt (asub (aint 1) (asq c))
  let Np := pairs (mhat (rsum rp (incRow0 c w)) mp) dp tl.1
  let den := asub (asq Zp.e0) (amul d2 (asq Zp.o0))
  let iden := arecip den
  let iz := (amul Zp.e0 iden, aneg (amul Zp.o0 iden))
  let mm := pmul d2 (Zp.e1, Zp.o1) iz
  let m2 := psq d2 mm
  let x2 := pmul d2 (Zp.e2, Zp.o2) iz
  let vv := (asub x2.1 m2.1, asub x2.2 m2.2)
  let pp := pmul d2 (Np.e0, Np.o0) iz
  let aa := pmul d2 (Np.e1, Np.o1) iz
  let bb := pmul d2 (Np.e2, Np.o2) iz
  let Uo := asub (aadd (asub bb.2 (amulN (pmul2 mm aa) 2)) (pmul2 m2 pp)) (pmul2 pp vv)
  let q := amul (amul (amul (aexp (amul (aadd m dv) c)) w) (aphi (amul rr w))) (arecip (aadd Zp.e0 (amul dv Zp.o0)))
  aadd (amulN Uo 2) (amulN (amul q (asq mm.2)) 2)

/-- the box test: every guard held, and c + |a1| + |a2| + |a3| + e < 0 -/
def check (b : Box) : Bool :=
  let g := gform b
  g.ok && zlt (ahi g) (zof 0)

def toInt (x : Z) : Int := bif x.neg then Int.neg (Int.ofNat x.mag) else Int.ofNat x.mag
/-- the five integers of G and the box test, for comparison with G_affine_reference.txt -/
def out (b : Box) : Int × Int × Int × Int × Nat × Bool :=
  let g := gform b
  (toInt g.c, toInt g.a1, toInt g.a2, toInt g.a3, g.e, g.ok && zlt (ahi g) (zof 0))

end GAff
