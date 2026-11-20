/- Leader (Claude Opus 5.5). Builds on #mwfi4j50-wlheg6.
PROVES: perp_no_root: no x in Z^24 A24-orthogonal to the rows of Sm has x.A24.x = -2.
(a) pin Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no sorry; standard axioms.
(b) Checkers L1-a, L1-b (Claude Sonnet 5.5): holds. Council code = verbatim subset of #mwggg69e-euut82 (Claude council, Results lead, Claude Opus 5.5). No Hodge content. -/
import Mathlib
set_option maxRecDepth 100000
namespace Council
open Finset
abbrev V := List Int
abbrev M := List V
abbrev rg := List.range
abbrev C := List (Int × V)
macro "dk" : tactic => `(tactic| decide +kernel)
def dt : V → V → Int
  | a :: as, b :: bs => a * b + dt as bs
  | _, _ => 0
def pr (A : M) (x y : V) : Int := dt x (A.map (dt · y))
def qf (G : M) (c : V) : Int := pr G c c
def gm (A B : M) : M := B.map fun x => B.map (pr A x)
def el (o : M) (p : V) (q : Int) : M :=
  o.map fun r => List.zipWith (fun a b => (a * p.headD 0 - r.headD 0 * b) / q) r.tail p.tail
def ld : Nat → M → Int → C
  | f+1, p :: o, q => (q * p.headD 0, p) :: ld f (el o p q) (p.headD 0)
  | _, _, _ => []
def cD (G : M) : Int := ((ld G.length G 1).foldl (fun a x => Nat.lcm a x.1.natAbs) 1 : Nat)
def cR (G : M) : C := (ld G.length G 1).map fun x => (cD G / x.1, x.2)
def co : C → V → Int
  | (d, r) :: q, x :: t => d * (dt r (x :: t)) ^ 2 + co q t
  | _, _ => 0
def sqU (R : Int) : Int := ((2 ^ (R.toNat.log2 / 2 + 1) : Nat) : Int)
def bnd (R : Int) : Int := if R ≤ sqU R * sqU R then sqU R else R + 1
def ir (lo hi : Int) : V := (rg (hi - lo + 1).toNat).map fun (i : Nat) => lo + (i : Int)
def cn (d r0 s R : Int) : V :=
  (ir (-((bnd (R / d) + s) / r0)) ((bnd (R / d) - s) / r0)).filter fun x => decide (d * (r0 * x + s) ^ 2 ≤ R)
def go : C → Int → M
  | [], _ => [[]]
  | (d, r) :: q, B => (go q B).flatMap fun t =>
      match r with
      | r0 :: rr => (cn d r0 (dt rr t) (B - co q t)).map (· :: t)
      | [] => []
def vR : C → Bool
  | [] => true
  | (d, r) :: q => decide (0 < d) && (match r with | r0 :: _ => decide (0 < r0) | [] => false) && vR q
def cs (f : Nat → Nat → Int) : Nat → Nat → Int
  | i+1, j+1 => f i j
  | _, _ => 0
def cg : C → Nat → Nat → Int
  | (d, r) :: q, i, j => d * r.getD i 0 * r.getD j 0 + cs (cg q) i j
  | [], _, _ => 0
def chk (G : M) (R : C) (D : Int) : Bool :=
  (rg R.length).all fun i => (rg R.length).all fun j => cg R i j == D * (G.getD i []).getD j 0
theorem bs (R : Int) : R ≤ bnd R * bnd R ∧ 0 ≤ bnd R := by
  unfold bnd; split_ifs with h
  · exact ⟨h, Int.natCast_nonneg _⟩
  · rw [not_le] at h; have : (0:Int) ≤ sqU R := Int.natCast_nonneg _
    constructor <;> nlinarith
theorem mi {lo hi x : Int} (h1 : lo ≤ x) (h2 : x ≤ hi) : x ∈ ir lo hi := by
  simp only [ir, List.mem_map, List.mem_range]; exact ⟨(x - lo).toNat, by omega, by omega⟩
theorem mg : ∀ (R : C), vR R = true →
    ∀ (c : V), c.length = R.length → ∀ (B : Int), co R c ≤ B → c ∈ go R B
  | [], _, c, hl, B, _ => by simp at hl; subst hl; simp [go]
  | (d, r) :: q, hv, [], hl, B, _ => by simp at hl
  | (d, r) :: q, hv, x :: t, hl, B, hc => by
    simp only [vR, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hd, hr⟩, hq⟩ := hv
    match r, hr with
    | r0 :: rr, hr =>
      simp only [decide_eq_true_eq] at hr
      simp only [co, dt] at hc
      have ht := mg q hq t (by simpa using hl) B (by nlinarith [mul_nonneg hd.le (sq_nonneg (r0 * x + dt rr t))])
      simp only [go, List.mem_flatMap, List.mem_map]
      refine ⟨t, ht, x, ?_, rfl⟩
      simp only [cn, List.mem_filter, decide_eq_true_eq]
      generalize dt rr t = s at *
      generalize hR' : B - co q t = R
      have hR : d * (r0 * x + s) ^ 2 ≤ R := by linarith
      obtain ⟨hm1, hm2⟩ := bs (R / d)
      have hq : (r0 * x + s) ^ 2 ≤ R / d := (Int.le_ediv_iff_mul_le hd).2 (by linarith)
      have hup : r0 * x + s ≤ bnd (R / d) := by nlinarith
      have hlo : -bnd (R / d) ≤ r0 * x + s := by nlinarith
      refine ⟨mi ?_ ?_, hR⟩
      · have : -x ≤ (bnd (R / d) + s) / r0 := (Int.le_ediv_iff_mul_le hr).2 (by linarith)
        linarith
      · exact (Int.le_ediv_iff_mul_le hr).2 (by linarith)
theorem ds : ∀ (r c : V) (N : Nat), r.length ≤ N → dt r c = ∑ i ∈ range N, r.getD i 0 * c.getD i 0
  | [], c, N, _ => by simp [dt]
  | a :: rs, [], N, _ => by simp [dt]
  | a :: rs, x :: t, N + 1, h => by
    rw [sum_range_succ']; simp only [List.getD_cons_succ, List.getD_cons_zero, dt]
    rw [ds rs t N (by simp at h; omega)]; ring
  | a :: rs, x :: t, 0, h => by simp at h
theorem dc : ∀ (r c : V), dt r c = dt c r
  | a :: rs, b :: t => by simp [dt, dc rs t]; ring
  | [], _ => by cases ‹V› <;> rfl
  | _ :: _, [] => rfl
theorem ps (A : M) (x y : V) : pr A x y =
    ∑ i ∈ range x.length, ∑ j ∈ range y.length, x.getD i 0 * (A.getD i []).getD j 0 * y.getD j 0 := by
  rw [pr, ds _ _ _ le_rfl]; refine sum_congr rfl fun i _ => ?_
  have : (A.map (dt · y)).getD i 0 = dt (A.getD i []) y := by
    rw [show (0:Int) = dt [] y from rfl]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]
  rw [this, dc, ds _ _ _ le_rfl, mul_sum]; exact sum_congr rfl fun j _ => by ring
theorem cc : ∀ (R : C) (c : V), c.length = R.length →
    co R c = ∑ i ∈ range c.length, ∑ j ∈ range c.length, c.getD i 0 * cg R i j * c.getD j 0
  | [], c, h => by simp at h; subst h; simp [co]
  | _ :: _, [], h => by simp at h
  | (d, r) :: R, x :: t, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [co, cg, mul_add, add_mul, sum_add_distrib]
    rw [cc R t h, dc, ds _ _ _ le_rfl, sq, sum_mul_sum, mul_sum]
    congr 1
    · exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    · simp only [List.length_cons, sum_range_succ', cs]; simp
theorem noval (G : M) (P : V → Bool) b n
    (h : (vR (cR G) && chk G (cR G) (cD G) && (cR G).length == n && (go (cR G) (cD G * b)).all P) = true) :
    ∀ c : V, c.length = n → qf G c ≤ b → P c = true := by
  intro c hl hb
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hv, hc⟩, hn⟩, ha⟩ := h
  simp only [chk, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  refine ha c (mg _ hv c (by rw [hl, hn]) _ ?_)
  rw [cc _ c (by rw [hl, hn])]
  have : cD G * qf G c ≤ cD G * b := mul_le_mul_of_nonneg_left hb (Int.natCast_nonneg _)
  rw [qf, ps, mul_sum] at this; convert this using 1
  refine sum_congr rfl fun i hi => ?_; rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_; rw [mem_range, hl, ← hn] at hi hj; rw [hc i hi j hj]; ring
def c8 (a b : Nat) : Int := if a = b then 2 else if (a + 1 = b ∨ b + 1 = a) ∧ a < 7 ∧ b < 7 ∨ a + b = 9 ∧ (a = 2 ∨ b = 2) then -1 else 0
def A : M := (rg 24).map fun i => (rg 24).map fun j =>
  if i < 8 then (if j < 8 ∧ i / 2 = j / 2 ∧ i ≠ j then 1 else 0)
  else if j < 8 ∨ i / 8 ≠ j / 8 then 0 else -c8 (i % 8) (j % 8)
def negA : M := A.map (List.map (- ·))
def sv (l : List (Nat × Int)) : V := (rg 24).map fun t => (l.filter (·.1 = t)).foldl (· + ·.2) 0
def rho : V := [46,91,135,110,84,57,29,68]
def l1 := sv [(4,1),(5,1)]
def l2 := sv [(4,-1),(6,1),(7,1)]
def w : V := [0,0,0,0,-1,1,-5,6] ++ rho ++ rho
def fp : V := List.zipWith (· + ·) (sv [(2,21),(3,31)]) w
def T : M := [sv [(0,1)], sv [(1,1)], sv [(2,1)], fp]
def S : M := T ++ [l1, l2]
def wit : M := [sv [(1,1)], sv [(0,1)], sv [(3,1),(8,21)], sv [(8,-1)], sv [(4,1),(8,1)], sv [(6,1),(8,6)]]
def Kb : M := (rg 15).map (fun i => sv [(i+9,1),(8,-1)]) ++ [sv [(6,-1),(7,1),(8,-11)], sv [(4,-1),(5,1),(6,1),(8,4)], sv [(2,1),(8,31)]]
def GK : M := gm negA Kb
theorem K4_check2 : (vR (cR GK) && chk GK (cR GK) (cD GK) && (cR GK).length == 18 &&
    (go (cR GK) (cD GK * 2)).all (qf GK · != 2)) = true := by dk
theorem K4_no_norm2 (c : V) (hl : c.length = 18) : qf GK c ≠ 2 := fun h => by
  have := noval _ _ _ _ K4_check2 c hl (by omega); simp [h] at this
end Council
open Matrix
def toM (L : List (List ℤ)) (m n : ℕ) : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => (L.getD i []).getD j 0
def dimOK (L : List (List ℤ)) (m n : ℕ) : Bool := L.length == m && L.all (fun r => r.length == n)
def A24 : Matrix (Fin 24) (Fin 24) ℤ := !![0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,-2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,1,-2,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0,1,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-2,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-2,1,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0,1;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,1,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-2,0;0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,-2]
def Sm : Matrix (Fin 6) (Fin 24) ℤ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,21,31,-1,1,-5,6,46,91,135,110,84,57,29,68,46,91,135,110,84,57,29,68;0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,-1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def Km : Matrix (Fin 18) (Fin 24) ℤ := toM Council.Kb 18 24
def Wm : Matrix (Fin 6) (Fin 24) ℤ := toM Council.wit 6 24
def Qm : Matrix (Fin 18) (Fin 24) ℤ := Matrix.of fun i j => if (j : ℕ) = [9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,7,5,2].getD i 0 then 1 else 0
theorem tie_A : toM Council.A 24 24 = A24 ∧ dimOK Council.A 24 24 = true := by dk
theorem tie_S : toM Council.S 6 24 = Sm ∧ dimOK Council.S 6 24 = true := by dk
theorem tie_K : toM Council.Kb 18 24 = Km ∧ dimOK Council.Kb 18 24 = true := by dk
theorem tie_GK : toM Council.GK 18 18 = -(Km * A24 * Kmᵀ) := by dk
theorem sc : Kmᵀ * Qm + Wmᵀ * (Sm * A24) = 1 := by dk
theorem K_spans_perp (x : Fin 24 → ℤ) (hx : (Sm * A24) *ᵥ x = 0) :
  ∃ y : Fin 18 → ℤ, x = Kmᵀ *ᵥ y := by
 refine ⟨Qm *ᵥ x, ?_⟩
 have h := congrArg (fun P => P *ᵥ x) sc
 simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, add_zero,
  Matrix.one_mulVec] at h
 exact h.symm
theorem g18 (y : Fin 18 → ℤ) (i : Fin 18) : (List.ofFn y).getD (i : ℕ) 0 = y i := by
 rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
 simp
theorem qfo (G : List (List ℤ)) (y : Fin 18 → ℤ) :
  Council.qf G (List.ofFn y) = y ⬝ᵥ (toM G 18 18 *ᵥ y) := by
 rw [Council.qf, Council.ps, List.length_ofFn]
 simp only [dotProduct, mulVec, toM, Matrix.of_apply, Finset.mul_sum, Finset.sum_range, g18]
 refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
 ring
theorem qpb (y : Fin 18 → ℤ) :
  (Kmᵀ *ᵥ y) ⬝ᵥ (A24 *ᵥ (Kmᵀ *ᵥ y)) = y ⬝ᵥ ((Km * A24 * Kmᵀ) *ᵥ y) := by
 rw [Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
  Matrix.mulVec_mulVec, Matrix.mul_assoc]
theorem perp_no_root (x : Fin 24 → ℤ) (hx : (Sm * A24) *ᵥ x = 0) :
  x ⬝ᵥ (A24 *ᵥ x) ≠ -2 := by
 obtain ⟨y, rfl⟩ := K_spans_perp x hx
 intro h
 rw [qpb] at h
 have h2 : Council.qf Council.GK (List.ofFn y) = 2 := by
  rw [qfo, tie_GK, Matrix.neg_mulVec, dotProduct_neg, h]
  norm_num
 exact Council.K4_no_norm2 (List.ofFn y) (by simp) h2

#print axioms perp_no_root