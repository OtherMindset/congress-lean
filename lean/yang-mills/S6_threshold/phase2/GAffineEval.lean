/-!
# Phase 2: `Eval` for the affine certificate (one box)

The same algorithm and the same rounding as `python/yang-mills/S6_threshold/G_affine_cert.py` at commit
95d0843, written for Lean's kernel (spec §3.1): natural numbers only, a signed integer being a sign and a
magnitude; rounding by shifts with P = 64; comparisons by `Nat.ble` and `Nat.beq`; no type-class
operations on integers. Lean 4, no Mathlib. There is no soundness proof here. Lattice only.

Notation. S = 2^64. A form `⟨c, a1, a2, a3, e⟩` stands for the set of reals X with
|S X - (c + a1 ε1 + a2 ε2 + a3 ε3)| ≤ e; R = |a1| + |a2| + |a3| + e, lo = c - R, hi = c + R.
Every rule is that of the README's "Arithmetic rules"; the comments give the formula each line computes.
-/
namespace GAff

local infixl:65 " +ₙ " => Nat.add
local infixl:65 " -ₙ " => Nat.sub
local infixl:70 " *ₙ " => Nat.mul
local infixl:70 " /ₙ " => Nat.div

/-- S = 2^P, P = 64; `SS` = S², `S1` = S - 1 and `T1` = 2S - 1 (for rounding up by shifts). -/
def S : Nat := Nat.shiftLeft 1 64
def SS : Nat := S *ₙ S
def S1 : Nat := S -ₙ 1
def T1 : Nat := Nat.shiftLeft 1 65 -ₙ 1

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n +ₙ 1) *ₙ fact n

def bxor : Bool → Bool → Bool
  | true, true => false
  | true, false => true
  | false, b => b

/-! ## Signed integers: (-1)^neg · mag -/

structure Z where
  neg : Bool
  mag : Nat

def zof (n : Nat) : Z := ⟨false, n⟩
def z0 : Z := ⟨false, 0⟩
def zneg (x : Z) : Z := ⟨!x.neg, x.mag⟩
def zadd (x y : Z) : Z :=
  bif bxor x.neg y.neg then
    (bif Nat.ble y.mag x.mag then ⟨x.neg, x.mag -ₙ y.mag⟩ else ⟨y.neg, y.mag -ₙ x.mag⟩)
  else ⟨x.neg, x.mag +ₙ y.mag⟩
def zsub (x y : Z) : Z := zadd x (zneg y)
def zmul (x y : Z) : Z := ⟨bxor x.neg y.neg, x.mag *ₙ y.mag⟩
def zmulN (x : Z) (k : Nat) : Z := ⟨x.neg, x.mag *ₙ k⟩
/-- ⌊x / 2^k⌋ (Python's `x >> k`): a negative x rounds away from zero. -/
def zshr (x : Z) (k : Nat) : Z :=
  bif x.neg then ⟨true, Nat.shiftRight (x.mag +ₙ (Nat.shiftLeft 1 k -ₙ 1)) k⟩
  else ⟨false, Nat.shiftRight x.mag k⟩
/-- ⌊x / n⌋ for n > 0 (Python's `x // n`). -/
def zdiv (x : Z) (n : Nat) : Z :=
  bif x.neg then ⟨true, (x.mag +ₙ (n -ₙ 1)) /ₙ n⟩ else ⟨false, x.mag /ₙ n⟩
/-- ⌈a / n⌉ for n > 0. -/
def cdivN (a n : Nat) : Nat := (a +ₙ (n -ₙ 1)) /ₙ n
def nonneg (x : Z) : Bool := !x.neg || Nat.beq x.mag 0
def zle (x y : Z) : Bool := nonneg (zsub y x)
def zlt (x y : Z) : Bool := !(zle y x)
/-- For statements only; not used by the evaluator. -/
def Z.toInt (x : Z) : Int := bif x.neg then -(x.mag : Int) else (x.mag : Int)

/-! ## Exact rationals n / d (d > 0, not reduced): only their values matter -/

structure Q where
  n : Z
  d : Nat

def qN (a b : Nat) : Q := ⟨zof a, b⟩
def half : Q := qN 1 2
def qadd (a b : Q) : Q := ⟨zadd (zmulN a.n b.d) (zmulN b.n a.d), a.d *ₙ b.d⟩
def qneg (a : Q) : Q := ⟨zneg a.n, a.d⟩
def qsub (a b : Q) : Q := qadd a (qneg b)
def qmul (a b : Q) : Q := ⟨zmul a.n b.n, a.d *ₙ b.d⟩
/-- S·a -/
def qS (a : Q) : Q := ⟨zmulN a.n S, a.d⟩
def qle (a b : Q) : Bool := zle (zmulN a.n b.d) (zmulN b.n a.d)
def qlt (a b : Q) : Bool := !(qle b a)
def qmin (a b : Q) : Q := bif qle a b then a else b
def qmax (a b : Q) : Q := bif qle a b then b else a
def qfloor (a : Q) : Z := zdiv a.n a.d
def qceil (a : Q) : Z := zneg (zdiv (zneg a.n) a.d)

/-! ## Elementary functions on rationals -/

/-- Horner: 1 + q(1 + q/2(1 + … (1 + q/40))) = Σ_{j ≤ 40} q^j / j!, for q = a / b. -/
def expLoop (a : Z) (b : Nat) : Nat → Q → Q
  | 0, t => t
  | j + 1, t => let u := b *ₙ (j +ₙ 1) *ₙ t.d; expLoop a b j ⟨zadd (zof u) (zmul a t.n), u⟩
/-- `exp_iv`: e^q ∈ [s - r, s + r], r = 8 · 2^41 / 41!, for |q| ≤ 2. -/
def EXPR : Q := qN (8 *ₙ Nat.shiftLeft 1 41) (fact 41)
def expIv (a : Z) (b : Nat) : Q × Q :=
  let s := expLoop a b 40 (qN 1 1)
  (qsub s EXPR, qadd s EXPR)
def expOk (a : Z) (b : Nat) : Bool := Nat.ble a.mag (2 *ₙ b)
/-- `cosh_hi`: (exp_hi(q) + exp_hi(-q)) / 2. -/
def coshHi (a : Z) (b : Nat) : Q := qmul (qadd (expIv a b).2 (expIv (zneg a) b).2) half

/-- Horner in q²: Σ_{k ≤ 30} C_k q^(2k) with C_k = (2k)!/(4^k k!² (2k+1)), since
C_{k+1} / C_k = (2k+1)² / ((2k+2)(2k+3)); here a2 / b2 = q². -/
def asinLoop (a2 b2 : Nat) : Nat → Nat → Nat → Q
  | 0, tn, td => qN tn td
  | k + 1, tn, td =>
    let u := (2 *ₙ k +ₙ 2) *ₙ (2 *ₙ k +ₙ 3) *ₙ b2 *ₙ td
    asinLoop a2 b2 k (u +ₙ (2 *ₙ k +ₙ 1) *ₙ (2 *ₙ k +ₙ 1) *ₙ a2 *ₙ tn) u
/-- `asin_iv` for q = a / b ≥ 0: asin q ∈ [s, s + q^63 / (1 - q²)], s = q · Σ C_k q^(2k). -/
def asinPos (a b : Nat) : Q × Q :=
  let s := qmul (qN a b) (asinLoop (a *ₙ a) (b *ₙ b) 30 1 1)
  (s, qadd s (qN (Nat.pow a 63) (Nat.pow b 61 *ₙ (b *ₙ b -ₙ a *ₙ a))))
/-- asin is odd. -/
def asinIv (v : Z) (b : Nat) : Q × Q :=
  let r := asinPos v.mag b
  bif v.neg then (qneg r.2, qneg r.1) else r

/-- Partial sum s_n of atan(1/m) = Σ_j (-1)^j / ((2j+1) m^(2j+1)), as N / (M · P) with M = m^(2k+1),
P = 1·3·…·(2k+1); one step adds (-1)^(k+1) / ((2k+3) m^(2k+3)): N ↦ N m² (2k+3) ± P. -/
def atanLoop (m2 : Nat) : Nat → Nat → Z → Nat → Nat → Q
  | 0, _, N, P, M => ⟨N, M *ₙ P⟩
  | f + 1, k, N, P, M =>
    atanLoop m2 f (k +ₙ 1) (zadd (zmulN N (m2 *ₙ (2 *ₙ k +ₙ 3))) ⟨Nat.beq (Nat.mod k 2) 0, P⟩)
      (P *ₙ (2 *ₙ k +ₙ 3)) (M *ₙ m2)
def atanS (m n : Nat) : Q := atanLoop (m *ₙ m) n 0 (zof 1) 1 m
/-- `atan_fr`: hull of the last two partial sums. -/
def atanIv (m n : Nat) : Q × Q :=
  let a := atanS m (n -ₙ 1)
  let b := atanS m n
  (qmin a b, qmax a b)
/-- Machin: π = 16 atan(1/5) - 4 atan(1/239). -/
def PIlo : Q := qsub (qmul (qN 16 1) (atanIv 5 40).1) (qmul (qN 4 1) (atanIv 239 20).2)
def PIhi : Q := qsub (qmul (qN 16 1) (atanIv 5 40).2) (qmul (qN 4 1) (atanIv 239 20).1)

/-! ## Affine forms -/

structure AF where
  c : Z
  a1 : Z
  a2 : Z
  a3 : Z
  e : Nat

def AF.R (x : AF) : Nat := x.a1.mag +ₙ x.a2.mag +ₙ x.a3.mag +ₙ x.e
def AF.lo (x : AF) : Z := zsub x.c (zof x.R)
def AF.hi (x : AF) : Z := zadd x.c (zof x.R)
def aZ : AF := ⟨z0, z0, z0, z0, 0⟩
/-- the integer k, exactly: ⟨k S, 0, 0, 0, 0⟩ -/
def cvN (k : Nat) : AF := ⟨zof (Nat.shiftLeft k 64), z0, z0, z0, 0⟩
def aadd (x y : AF) : AF := ⟨zadd x.c y.c, zadd x.a1 y.a1, zadd x.a2 y.a2, zadd x.a3 y.a3, x.e +ₙ y.e⟩
def aneg (x : AF) : AF := ⟨zneg x.c, zneg x.a1, zneg x.a2, zneg x.a3, x.e⟩
def asub (x y : AF) : AF := aadd x (aneg y)
def asmul (x : AF) (k : Nat) : AF := ⟨zmulN x.c k, zmulN x.a1 k, zmulN x.a2 k, zmulN x.a3 k, x.e *ₙ k⟩
/-- X / n: four floors, e ↦ ⌈e/n⌉ + 4. -/
def adiv (x : AF) (n : Nat) : AF := ⟨zdiv x.c n, zdiv x.a1 n, zdiv x.a2 n, zdiv x.a3 n, cdivN x.e n +ₙ 4⟩
def awid (x : AF) (t : Nat) : AF := ⟨x.c, x.a1, x.a2, x.a3, x.e +ₙ t⟩
/-- MUL: centre ⌊cx cy / S⌋, linear ⌊(cx ay + cy ax) / S⌋,
e = ⌈(|cx| ey + |cy| ex + Rx Ry) / S⌉ + 4. -/
def amul (x y : AF) : AF :=
  let num := x.c.mag *ₙ y.e +ₙ y.c.mag *ₙ x.e +ₙ x.R *ₙ y.R
  ⟨zshr (zmul x.c y.c) 64, zshr (zadd (zmul x.c y.a1) (zmul y.c x.a1)) 64,
   zshr (zadd (zmul x.c y.a2) (zmul y.c x.a2)) 64, zshr (zadd (zmul x.c y.a3) (zmul y.c x.a3)) 64,
   Nat.shiftRight (num +ₙ S1) 64 +ₙ 4⟩
/-- SQ: (A + u)² ∈ [0, R²], so centre ⌊(2cx² + R²) / 2S⌋, linear ⌊2 cx ai / S⌋,
e = ⌈(R² + 4|cx| ex) / 2S⌉ + 4. -/
def asq (x : AF) : AF :=
  let R := x.R
  ⟨zof (Nat.shiftRight (2 *ₙ (x.c.mag *ₙ x.c.mag) +ₙ R *ₙ R) 65),
   zshr (zmul x.c x.a1) 63, zshr (zmul x.c x.a2) 63, zshr (zmul x.c x.a3) 63,
   Nat.shiftRight (R *ₙ R +ₙ 4 *ₙ (x.c.mag *ₙ x.e) +ₙ T1) 65 +ₙ 4⟩
/-- `const`: centre ⌊S (lo + hi)/2⌋, e = ⌈S (hi - lo)/2⌉ + 1. -/
def aconst (lo hi : Q) : AF :=
  ⟨qfloor (qS (qmul (qadd lo hi) half)), z0, z0, z0, (qceil (qS (qmul (qsub hi lo) half))).mag +ₙ 1⟩
/-- `var`: centre ⌊S (lo + hi)/2⌋ and coefficient ⌈S (hi - lo)/2⌉ + 1. -/
def avar (lo hi : Q) : Z × Z :=
  (qfloor (qS (qmul (qadd lo hi) half)), zadd (qceil (qS (qmul (qsub hi lo) half))) (zof 1))

/-! ## The function rule: f(X) = α X + g(X), g = f - α·id monotone on [lo, hi] -/

/-- hull of g = f - (al/S)·id at the two ends, from enclosures [f0l, f0h] of f(lo), [f1l, f1h] of f(hi) -/
def gHull (lo hi : Z) (f0l f0h f1l f1h : Q) (al : Z) : Q × Q :=
  let s0 : Q := ⟨zmul al lo, S⟩
  let s1 : Q := ⟨zmul al hi, S⟩
  let g0 := qsub f0l s0
  let g1 := qsub f0h s0
  let g2 := qsub f1l s1
  let g3 := qsub f1h s1
  (qmin (qmin (qmin g0 g1) g2) g3, qmax (qmax (qmax g0 g1) g2) g3)
/-- Both slopes are formed; the second is kept only if its hull is strictly narrower. -/
def fnRule (x : AF) (f0l f0h f1l f1h : Q) (alo ahi : Z) : AF :=
  let lo := x.lo
  let hi := x.hi
  let A := gHull lo hi f0l f0h f1l f1h alo
  let B := gHull lo hi f0l f0h f1l f1h ahi
  let useB := qlt (qsub B.2 B.1) (qsub A.2 A.1)
  let al := bif useB then ahi else alo
  let gl := bif useB then B.1 else A.1
  let gh := bif useB then B.2 else A.2
  let y := amul x ⟨al, z0, z0, z0, 0⟩
  ⟨zadd y.c (qfloor (qmul (qadd gl gh) half)), y.a1, y.a2, y.a3,
   y.e +ₙ (qceil (qmul (qsub gh gl) half)).mag +ₙ 1⟩

/-- 1/x on lo > 0: f = S²/v; slopes -⌈S³/lo²⌉ and -⌊S³/hi²⌋. -/
def recipPos (x : AF) : AF :=
  let lo := x.lo.mag
  let hi := x.hi.mag
  let S3 := SS *ₙ S
  fnRule x (qN SS lo) (qN SS lo) (qN SS hi) (qN SS hi) ⟨true, cdivN S3 (lo *ₙ lo)⟩ ⟨true, S3 /ₙ (hi *ₙ hi)⟩
/-- 1/x = -(1/(-x)) when hi < 0. -/
def arecip (x : AF) : AF := bif zlt x.hi z0 then aneg (recipPos (aneg x)) else recipPos x
def recipOk (x : AF) : Bool := zlt x.hi z0 || zlt z0 x.lo

/-- ⌊√n⌋ by Newton from 2^(⌊log2 n / 2⌋ + 1) > √n. -/
def isqrtLoop (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x =>
    let y := Nat.shiftRight (x +ₙ n /ₙ x) 1
    bif Nat.blt y x then isqrtLoop n f y else x
def isqrt (n : Nat) : Nat :=
  bif Nat.beq n 0 then 0 else isqrtLoop n 200 (Nat.shiftLeft 1 (Nat.shiftRight (Nat.log2 n) 1 +ₙ 1))
/-- ⌈√n⌉ -/
def csqrt (n : Nat) : Nat := let a := isqrt n; bif Nat.beq (a *ₙ a) n then a else a +ₙ 1
/-- √x: f(v) ∈ [⌊√(vS)⌋, ⌈√(vS)⌉]; slopes ⌊S²/(2⌈√(hi S)⌉)⌋ and ⌈S²/(2⌊√(lo S)⌋)⌉. -/
def asqrt (x : AF) : AF :=
  let lS := x.lo.mag *ₙ S
  let hS := x.hi.mag *ₙ S
  let rl := isqrt lS
  let rh := csqrt hS
  fnRule x (qN rl 1) (qN (csqrt lS) 1) (qN (isqrt hS) 1) (qN rh 1)
    (zof (SS /ₙ (2 *ₙ rh))) (zof (cdivN SS (2 *ₙ rl)))
def sqrtOk (x : AF) : Bool := zlt z0 x.lo && Nat.blt 0 (isqrt (x.lo.mag *ₙ S))

/-- eˣ: f(v) = S·exp_iv(v/S); slopes ⌊S e^lo⌋ and ⌈S e^hi⌉ (from the same enclosures). -/
def aexp (x : AF) : AF :=
  let e0 := expIv x.lo S
  let e1 := expIv x.hi S
  fnRule x (qS e0.1) (qS e0.2) (qS e1.1) (qS e1.2) (qfloor (qS e0.1)) (qceil (qS e1.2))
def expRuleOk (x : AF) : Bool := expOk x.lo S && expOk x.hi S

/-- asin: f(v) = S·asin_iv(v/S); with m = min|y| (0 if lo ≤ 0 ≤ hi) and M = max|y|,
slopes ⌊S²/⌈√(S² - m²)⌉⌋ and ⌈S²/⌊√(S² - M²)⌋⌉. -/
def aasin (x : AF) : AF :=
  let lo := x.lo
  let hi := x.hi
  let f0 := asinIv lo S
  let f1 := asinIv hi S
  let M := bif Nat.ble lo.mag hi.mag then hi.mag else lo.mag
  let m := bif zle lo z0 && zle z0 hi then 0 else (bif Nat.ble lo.mag hi.mag then lo.mag else hi.mag)
  fnRule x (qS f0.1) (qS f0.2) (qS f1.1) (qS f1.2)
    (zof (SS /ₙ csqrt (SS -ₙ m *ₙ m))) (zof (cdivN SS (isqrt (SS -ₙ M *ₙ M))))
/-- -S/4 ≤ lo and hi ≤ S/4 -/
def asinOk (x : AF) : Bool :=
  zle ⟨true, Nat.shiftLeft 1 62⟩ x.lo && zle x.hi (zof (Nat.shiftLeft 1 62))

/-! ## Tables, walked head first (no indexing) -/

def tl {α : Type} : List α → List α
  | _ :: t => t
  | [] => []
def drop2 {α : Type} : List α → List α
  | _ :: _ :: t => t
  | _ => []
def zipAdd : List AF → List AF → List AF
  | x :: xs, y :: ys => aadd x y :: zipAdd xs ys
  | _, _ => []
def zipSub : List AF → List AF → List AF
  | x :: xs, y :: ys => asub x y :: zipSub xs ys
  | _, _ => []
/-- one row of `ktab`: T[k][n] = T[k-1][n] - T[k-1][n+2] -/
def ktab (r : List AF) : List AF := zipSub r (drop2 r)
def zeros : Nat → List AF
  | 0 => []
  | n + 1 => aZ :: zeros n
/-- `powers`: [p, p x, p x², …] (n entries), from p = 1 -/
def powL (x : AF) : Nat → AF → List AF
  | 0, _ => []
  | n + 1, p => p :: powL x n (amul p x)

/-- The full table. Python's QFULL[k][n] (base[n] = base[n-2] (n-1)/(n+2), base[0] = 1/2, then `ktab`) is
T[k][n] = (1/π) ∫_{-1}^{1} xⁿ (1 - x²)^(k+1/2) dx, a Beta integral:
T[k][2j] = (2j-1)!! (2k+1)!! / (2^(j+k+1) (j+k+1)!), T[k][2j+1] = 0.
So T[k][2j+2] = T[k][2j] (2j+1) / (2(j+k+2)) along a row, and T[k+1][0] = T[k][0] (2k+3) / (2(k+2)).
(Equal to QFULL as rationals at every entry: phase2/full_table_check.py.)
FULLC[k][n] = const(π T / (2k+1)!) with π ∈ [PIlo, PIhi]; T ≥ 0, so Python's `sorted` keeps the order. -/
def fconst (t : Q) (f : Nat) : AF :=
  aconst (qmul (qmul t PIlo) (qN 1 f)) (qmul (qmul t PIhi) (qN 1 f))
/-- r^(2k) FULLC[k][n], n = 2j, 2j+1, …: two entries a step -/
def scaleFull (p : AF) (k f : Nat) : Nat → Nat → Q → List AF
  | 0, _, _ => []
  | s + 1, j, t =>
    amul p (fconst t f) :: amul p (fconst (qN 0 1) f) ::
      scaleFull p k f s (j +ₙ 1) (qmul t (qN (2 *ₙ j +ₙ 1) (2 *ₙ (j +ₙ k +ₙ 2))))
def scaleDiv (p : AF) (f : Nat) : List AF → List AF
  | x :: xs => adiv (amul p x) f :: scaleDiv p f xs
  | [] => []
/-- `rsum_full`: Σ_k r^(2k) FULLC[k][n], n ≤ 31; f = (2k+1)!, t0 = T[k][0] -/
def rsumFull (acc : List AF) (k f : Nat) (t0 : Q) : List AF → List AF
  | p :: ps =>
    rsumFull (zipAdd acc (scaleFull p k f 16 0 t0)) (k +ₙ 1) (f *ₙ (2 *ₙ k +ₙ 2) *ₙ (2 *ₙ k +ₙ 3))
      (qmul t0 (qN (2 *ₙ k +ₙ 3) (2 *ₙ (k +ₙ 2)))) ps
  | [] => acc
/-- `rsum`: Σ_k (r^(2k) T[k][n]) / (2k+1)!, n ≤ 31 -/
def rsumInc (acc : List AF) (i f : Nat) : List AF → List AF → List AF
  | p :: ps, row =>
    rsumInc (zipAdd acc (scaleDiv p f row)) (i +ₙ 1) (f *ₙ (2 *ₙ i +ₙ 2) *ₙ (2 *ₙ i +ₙ 3)) ps (ktab row)
  | [], _ => acc
/-- Σ_i (p_i g_i) / i! -/
def dotF (acc : AF) (i f : Nat) : List AF → List AF → AF
  | p :: ps, g :: gs => dotF (aadd acc (adiv (amul p g) f)) (i +ₙ 1) (f *ₙ (i +ₙ 1)) ps gs
  | _, _ => acc
/-- `mhat`: Mh[k] = Σ_{i ≤ 18} (μ^i G[k+i]) / i!, k ≤ 13 -/
def mhat (mp : List AF) : Nat → List AF → List AF
  | 0, _ => []
  | n + 1, G => dotF aZ 0 1 mp G :: mhat mp n (tl G)
/-- the pair (E, O) = (Σ_j (d^(2j) Mh[2j]) / (2j)!, Σ_j (d^(2j) Mh[2j+1]) / (2j+1)!) -/
def pairDot (ae ao : AF) (j f : Nat) : List AF → List AF → AF × AF
  | p :: ps, x :: y :: r =>
    let f1 := f *ₙ (2 *ₙ j +ₙ 1)
    pairDot (aadd ae (adiv (amul p x) f)) (aadd ao (adiv (amul p y) f1)) (j +ₙ 1) (f1 *ₙ (2 *ₙ j +ₙ 2)) ps r
  | _, _ => (ae, ao)
def pairN (dp : List AF) (tail : Nat) (Mh : List AF) : AF × AF :=
  let r := pairDot aZ aZ 0 1 dp Mh
  (awid r.1 tail, awid r.2 tail)
/-- `inc_table` base, n ≥ 2: base[n] encloses I_n = ∫_c^1 xⁿ √(1-x²) dx, w = √(1-c²), from
(n+2) I_n = (n-1) I_{n-2} + c^(n-1) w³, I_0 = π/4 - (c w + asin c)/2, I_1 = w³/3; then `ktab` gives
∫_c^1 xⁿ (1-x²)^(k+1/2) dx. Each step: base[n] = (base[n-2] (n-1) + c^(n-1) w³) / (n+2).
The running power is c, then c² by the square rule (Python's `c * c` is `sq`), then products. -/
def incBase (c w3 : AF) : Nat → Nat → AF → AF → AF → List AF
  | 0, _, _, _, _ => []
  | f + 1, n, b2, b1, cp =>
    let nx := adiv (aadd (asmul b2 (n -ₙ 1)) (amul cp w3)) (n +ₙ 2)
    nx :: incBase c w3 f (n +ₙ 1) b1 nx (bif Nat.beq n 2 then asq c else amul cp c)
/-- Σ_{k ≤ 7} z^(2k) / (2k+1)! -/
def phiLoop (z2 : AF) : Nat → Nat → Nat → AF → AF → AF
  | 0, _, _, s, _ => s
  | k + 1, i, f, s, p => phiLoop z2 k (i +ₙ 1) (f *ₙ (2 *ₙ i +ₙ 2) *ₙ (2 *ₙ i +ₙ 3)) (aadd s (adiv p f)) (amul p z2)
/-- atanh(√u)/√u = Σ_{k ≤ 12} u^k / (2k+1) -/
def atLoop (u2 : AF) : Nat → Nat → AF → AF → AF
  | 0, _, s, _ => s
  | k + 1, i, s, p => atLoop u2 k (i +ₙ 1) (aadd s (adiv p (2 *ₙ i +ₙ 1))) (amul p u2)

/-! ## One box -/

/-- pair product (a, b)(c, e) = (ac + d² be, ae + bc) -/
def pmul (d2 : AF) (x y : AF × AF) : AF × AF :=
  (aadd (amul x.1 y.1) (amul d2 (amul x.2 y.2)), aadd (amul x.1 y.2) (amul x.2 y.1))
/-- the pair square (Python's `mul(mm, mm)`, where `x * x` is `sq`) -/
def psq (d2 : AF) (x : AF × AF) : AF × AF :=
  let t := amul x.1 x.2
  (aadd (asq x.1) (amul d2 (asq x.2)), aadd t t)
/-- max(z, 0) -/
def pos (z : Z) : Nat := bif z.neg then 0 else z.mag

/-- μ ∈ [mln/mld, mhn/mhd], r ∈ [rln/rld, rhn/rhd], d ∈ [dln/dld, dhn/dhd] -/
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

structure Res where
  g : AF
  q : AF
  c : AF
  ok : Bool

/-- `G_affine`, with every guard of the Python program collected in `ok`. -/
def evalBox (b : Box) : Res :=
  let vm := avar (qN b.mln b.mld) (qN b.mhn b.mhd)
  let vr := avar (qN b.rln b.rld) (qN b.rhn b.rhd)
  let vd := avar (qN b.dln b.dld) (qN b.dhn b.dhd)
  let m : AF := ⟨vm.1, vm.2, z0, z0, 0⟩
  let rr : AF := ⟨vr.1, z0, vr.2, z0, 0⟩
  let dv : AF := ⟨vd.1, z0, z0, vd.2, 0⟩
  let d2 := asq dv
  let r2 := asq rr
  -- series tail 2 e^μ cosh d cosh r (d^12/12! + μ^19/19! + r^16/17!) at the upper corner
  let ch := qmul (qmul (qmul (qN 2 1) (expIv (zof b.mhn) b.mhd).2) (coshHi (zof b.dhn) b.dhd))
    (coshHi (zof b.rhn) b.rhd)
  let tq := qadd (qadd (qN (Nat.pow b.dhn 12) (Nat.pow b.dhd 12 *ₙ fact 12))
    (qN (Nat.pow b.mhn 19) (Nat.pow b.mhd 19 *ₙ fact 19))) (qN (Nat.pow b.rhn 16) (Nat.pow b.rhd 16 *ₙ fact 17))
  let tailZ := qceil (qS (qmul ch tq))
  let tail := tailZ.mag
  let rp := powL r2 8 (cvN 1)
  let mp := powL m 19 (cvN 1)
  let dp := powL d2 6 (cvN 1)
  let MF := mhat mp 14 (rsumFull (zeros 32) 0 1 half rp)
  let Z0 := pairN dp tail MF
  let X1 := pairN dp tail (tl MF)
  let X2 := pairN dp tail (drop2 MF)
  -- c = atanh(d t)/d = t Σ (d t)^(2k)/(2k+1), t = O0/E0, tail 2 u^13
  let t := amul Z0.2 (arecip Z0.1)
  let u2 := amul d2 (asq t)
  let a := awid (atLoop u2 13 0 aZ (cvN 1)) (cdivN (2 *ₙ Nat.pow (pos u2.hi) 13) (Nat.pow S 12))
  let c := amul t a
  let omc := asub (cvN 1) (asq c)
  let w := asqrt omc
  let w3 := amul (asq w) w
  let b0 := asub (aconst (qmul PIlo (qN 1 4)) (qmul PIhi (qN 1 4))) (adiv (aadd (amul c w) (aasin c)) 2)
  let b1 := adiv w3 3
  let MI := mhat mp 14 (rsumInc (zeros 32) 0 1 rp (b0 :: b1 :: incBase c w3 44 2 b0 b1 c))
  let N0 := pairN dp tail MI
  let N1 := pairN dp tail (tl MI)
  let N2 := pairN dp tail (drop2 MI)
  let den := asub (asq Z0.1) (amul d2 (asq Z0.2))
  let iden := arecip den
  let iz : AF × AF := (amul Z0.1 iden, aneg (amul Z0.2 iden))
  let mm := pmul d2 X1 iz
  let m2 := psq d2 mm
  let x2 := pmul d2 X2 iz
  let vv : AF × AF := (asub x2.1 m2.1, asub x2.2 m2.2)
  let pp := pmul d2 N0 iz
  let aa := pmul d2 N1 iz
  let bb := pmul d2 N2 iz
  let Uo := asub (aadd (asub bb.2 (asmul (pmul d2 mm aa).2 2)) (pmul d2 m2 pp).2) (pmul d2 pp vv).2
  -- φ(z) = sinh z / z, z = r w, tail z^16 cosh z / 17!
  let z := amul rr w
  let z2 := asq z
  let phT := qceil (qS (qmul (qN (Nat.pow (pos z2.hi) 8) (Nat.pow S 8 *ₙ fact 17)) (coshHi (zof (pos z.hi)) S)))
  let phi := awid (phiLoop z2 8 0 1 aZ (cvN 1)) phT.mag
  let ez := aadd Z0.1 (amul dv Z0.2)
  let ex := amul (aadd m dv) c
  let q := amul (amul (amul (aexp ex) w) phi) (arecip ez)
  let g := aadd (asmul Uo 2) (asmul (amul q (asq mm.2)) 2)
  let ok := qle PIlo PIhi && expOk (zof b.mhn) b.mhd && expOk (zof b.dhn) b.dhd && expOk (zof b.rhn) b.rhd &&
    nonneg tailZ && recipOk Z0.1 && zlt u2.hi (zof (Nat.shiftLeft 1 62)) &&
    zle ⟨true, Nat.shiftLeft 1 58⟩ c.lo && zle c.hi (zof (Nat.shiftLeft 1 62)) &&
    sqrtOk omc && asinOk c && recipOk den && expOk (zof (pos z.hi)) S && nonneg phT &&
    expRuleOk ex && recipOk ez
  ⟨g, q, c, ok⟩

/-- The box passes: hi(G) = c + |a1| + |a2| + |a3| + e < 0, and every guard holds. -/
def check (b : Box) : Bool :=
  let r := evalBox b
  zlt r.g.hi z0 && r.ok

/-- the five integers (c, a1, a2, a3, e) of the form of G, for the reference theorems -/
def form (b : Box) : Int × Int × Int × Int × Int :=
  let g := (evalBox b).g
  (g.c.toInt, g.a1.toInt, g.a2.toInt, g.a3.toInt, (g.e : Int))

end GAff
