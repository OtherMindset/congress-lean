/-!
Pilot only: a port of the evaluator of G_box_A_1of2.py (one box), to time Lean's kernel on it.
No soundness proof. Not a certificate.
-/
namespace GBox

def ONE : Int := 20282409603651670423947251286016  -- 2^104

structure V where
  l : Int
  h : Int

def cdiv (a n : Int) : Int := -((-a) / n)
def flq (num den : Int) : Int := (num * ONE) / den
def ceq (num den : Int) : Int := cdiv (num * ONE) den
def cvI (x : Int) : V := ⟨x * ONE, x * ONE⟩
def cvQ (num den : Int) : V := ⟨flq num den, ceq num den⟩
def add (s o : V) : V := ⟨s.l + o.l, s.h + o.h⟩
def sub (s o : V) : V := ⟨s.l - o.h, s.h - o.l⟩
def neg (s : V) : V := ⟨-s.h, -s.l⟩
def mul (s o : V) : V :=
  let p1 := s.l * o.l; let p2 := s.l * o.h; let p3 := s.h * o.l; let p4 := s.h * o.h
  ⟨(min (min p1 p2) (min p3 p4)) / ONE, cdiv (max (max p1 p2) (max p3 p4)) ONE⟩
def smul (n : Int) (s : V) : V := if 0 ≤ n then ⟨s.l * n, s.h * n⟩ else ⟨s.h * n, s.l * n⟩
def divN (s : V) (n : Int) : V := ⟨s.l / n, cdiv s.h n⟩
/-- division by an interval with positive lower end -/
def divI (s o : V) : V := mul s ⟨(ONE * ONE) / o.h, cdiv (ONE * ONE) o.l⟩
def sq (s : V) : V :=
  let a := s.l * s.l; let b := s.h * s.h
  ⟨(if s.l ≤ 0 ∧ 0 ≤ s.h then 0 else min a b) / ONE, cdiv (max a b) ONE⟩

def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x => let y := (x + n / x) / 2; if y < x then isqrtAux n f y else x
def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtAux n 400 (2 ^ (n.log2 / 2 + 1))
def isq (x : V) : V :=
  let lo := isqrt (x.l * ONE).toNat
  let hi := isqrt (x.h * ONE).toNat
  ⟨(lo : Int), if ((hi * hi : Nat) : Int) < x.h * ONE then ((hi + 1 : Nat) : Int) else (hi : Int)⟩

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
def F (n : Nat) : Int := fact n

def pw (x : V) (n : Nat) : V := (List.range n).foldl (fun r _ => mul r x) (cvI 1)

def EXP_R : Int := 1
def ser (a : Int) : V :=
  let av : V := ⟨a, a⟩
  ((List.range 50).foldl (fun (st : V × V) j =>
      let t := divN (mul st.2 av) ((j + 1 : Nat) : Int); (add st.1 t, t)) (cvI 1, cvI 1)).1
def iexp (x : V) : V := ⟨(ser x.l).l - EXP_R, (ser x.h).h + EXP_R⟩

def PI : V := ⟨63719069007931157819013617823235, 63719069007931157819013617823236⟩

def asinC (k : Nat) : V := cvQ (F (2 * k)) ((4 : Int) ^ k * F k * F k * ((2 * k + 1 : Nat) : Int))
def iasin (c : V) : V :=
  let c2 := sq c
  let r := (List.range 41).foldl (fun (st : V × V) k => (add st.1 (mul st.2 (asinC k)), mul st.2 c2))
    (cvI 0, c)
  add r.1 ⟨0, ceq 16 (15 * 4 ^ 83)⟩

def JS : Nat := 18
def JD : Nat := 5
def KR : Nat := 7
def NK : Nat := 13
def NMAX : Nat := 31
def NB : Nat := 47

def Z0 : V := cvI 0
def at' (xs : List V) (i : Nat) : V := xs.getD i Z0
def at2 (xs : List (List V)) (k n : Nat) : V := at' (xs.getD k []) n

def ktabStep (prev : List V) : List V :=
  (List.range (prev.length - 2)).map fun n => sub (at' prev n) (at' prev (n + 2))
def ktab (base : List V) : List (List V) :=
  ((List.range KR).foldl (fun (st : List (List V) × List V) _ =>
      let nx := ktabStep st.2; (st.1 ++ [nx], nx)) ([base], base)).1

/-- build base[0..NB-1] from a two-term recurrence; `stepf n prev2` gives base[n] from base[n-2] -/
def buildBase (b0 b1 : V) (stepf : Nat → V → V) : List V :=
  ((List.range (NB - 2)).foldl (fun (st : List V × V × V) i =>
      let n := i + 2
      let nx := stepf n st.2.1
      (st.1 ++ [nx], st.2.2, nx)) ([b0, b1], b0, b1)).1

def fullTable : List (List V) :=
  ktab (buildBase (divN PI 2) (cvI 0) fun n p2 => divN (smul ((n - 1 : Nat) : Int) p2) ((n + 2 : Nat) : Int))

/-- inc_table, with the running power c^(n-1) threaded through -/
def incTable (c : V) : List (List V) :=
  let w := isq (sub (cvI 1) (sq c))
  let w3 := mul (mul w w) w
  let b0 := sub (divN PI 4) (divN (add (mul c w) (iasin c)) 2)
  let b1 := divN w3 3
  let r := (List.range (NB - 2)).foldl (fun (st : List V × V × V × V) i =>
      let n := i + 2
      let nx := divN (add (smul ((n - 1 : Nat) : Int) st.2.1) (mul st.2.2.2 w3)) ((n + 2 : Nat) : Int)
      (st.1 ++ [nx], st.2.2.1, nx, mul st.2.2.2 c)) ([b0, b1], b0, b1, c)
  ktab r.1

def rsum (tab : List (List V)) (r2 : V) : List V :=
  (List.range (NMAX + 1)).map fun n =>
    ((List.range (KR + 1)).foldl (fun (st : V × V) k =>
      (add st.1 (divN (mul st.2 (at2 tab k n)) (F (2 * k + 1))), mul st.2 r2)) (cvI 0, cvI 1)).1

def mhat (G : List V) (mu : V) : List V :=
  (List.range (NK + 1)).map fun k =>
    ((List.range (JS + 1)).foldl (fun (st : V × V) i =>
      (add st.1 (divN (mul st.2 (at' G (k + i))) (F i)), mul st.2 mu)) (cvI 0, cvI 1)).1

def pairN (Mh : List V) (d2 : V) (tail : Int) (n : Nat) : V × V :=
  let r := (List.range (JD + 1)).foldl (fun (st : V × V × V) j =>
      (add st.1 (divN (mul st.2.2 (at' Mh (n + 2 * j))) (F (2 * j))),
       add st.2.1 (divN (mul st.2.2 (at' Mh (n + 2 * j + 1))) (F (2 * j + 1))),
       mul st.2.2 d2)) (cvI 0, cvI 0, cvI 1)
  (add r.1 ⟨-tail, tail⟩, add r.2.1 ⟨-tail, tail⟩)

def phiIv (z : V) : V :=
  let z2 := sq z
  let r := (List.range (KR + 1)).foldl (fun (st : V × V) k =>
      (add st.1 (divN st.2 (F (2 * k + 1))), mul st.2 z2)) (cvI 0, cvI 1)
  let e := iexp z
  add r.1 ⟨0, (divN (divN (mul r.2 (add e (divI (cvI 1) e))) 2) (F (2 * KR + 3))).h⟩

def pmul (d2 : V) (x y : V × V) : V × V :=
  (add (mul x.1 y.1) (mul d2 (mul x.2 y.2)), add (mul x.1 y.2) (mul x.2 y.1))

structure Res where
  val : V
  q : V
  c : V
  ok : Bool

/-- one box: mu in [ml/mlq, mh/mhq] etc., all as rationals num/den -/
def gEnclosure (FULL : List (List V)) (mln mld mhn mhd rln rld rhn rhd dln dld dhn dhd : Int) : Res :=
  let mu_i : V := ⟨flq mln mld, ceq mhn mhd⟩
  let r_i : V := ⟨flq rln rld, ceq rhn rhd⟩
  let dv : V := ⟨flq dln dld, ceq dhn dhd⟩
  let d2 := sq dv
  let er := iexp r_i
  let em := iexp mu_i
  let r2 := sq r_i
  let ch := divN (add er (divI (cvI 1) er)) 2
  let GF := rsum FULL r2
  let MF := mhat GF mu_i
  let dhiV := cvQ dhn dhd
  let ed := iexp dhiV
  let tail := (mul (mul (divN (mul (smul 2 em) (add ed (divI (cvI 1) ed))) 2) ch)
      (add (add (divN (pw dhiV (2 * JD + 2)) (F (2 * JD + 2))) (divN (pw mu_i (JS + 1)) (F (JS + 1))))
        (divN (pw r_i (2 * KR + 2)) (F (2 * KR + 3))))).h
  let Z := pairN MF d2 tail 0
  let X1 := pairN MF d2 tail 1
  let X2 := pairN MF d2 tail 2
  let t := divI Z.2 Z.1
  let u2 := mul d2 (sq t)
  let ar := (List.range 13).foldl (fun (st : V × V) k =>
      (add st.1 (divN st.2 ((2 * k + 1 : Nat) : Int)), mul st.2 u2)) (cvI 0, cvI 1)
  let c0 := mul t (add ar.1 ⟨0, 2 * ar.2.h⟩)
  let c : V := ⟨max c0.l 0, c0.h⟩
  let NM := mhat (rsum (incTable c) r2) mu_i
  let N0 := pairN NM d2 tail 0
  let N1 := pairN NM d2 tail 1
  let N2 := pairN NM d2 tail 2
  let den := sub (sq Z.1) (mul d2 (sq Z.2))
  let iz : V × V := (divI Z.1 den, neg (divI Z.2 den))
  let m := pmul d2 X1 iz
  let m2 := pmul d2 m m
  let x2 := pmul d2 X2 iz
  let var : V × V := (sub x2.1 m2.1, sub x2.2 m2.2)
  let pp := pmul d2 N0 iz
  let aa := pmul d2 N1 iz
  let bb := pmul d2 N2 iz
  let Uo := sub (add (sub bb.2 (smul 2 (pmul d2 m aa).2)) (pmul d2 m2 pp).2) (pmul d2 pp var).2
  let w := isq (sub (cvI 1) (sq c))
  let zq := add Z.1 (mul dv Z.2)
  let q := divI (mul (mul (iexp (mul (add mu_i dv) c)) w) (phiIv (mul r_i w))) zq
  let val := add (smul 2 Uo) (smul 2 (mul q (sq m.2)))
  ⟨val, q, c, decide (0 < Z.1.l ∧ 0 < den.l ∧ 0 < zq.l ∧ u2.h < ONE / 4 ∧ 0 ≤ c0.h ∧ c0.h ≤ ONE / 4)⟩

def box1 : Res := gEnclosure fullTable 80 200 81 200 40 100 41 100 126 1000 154 1000

end GBox

/-! The kernel check of the one box (about 4 s beyond start-up on the machine it was written on). -/
set_option maxRecDepth 1000000 in
theorem box1_neg : (decide (GBox.box1.val.h < 0) && GBox.box1.ok) = true := by decide +kernel
