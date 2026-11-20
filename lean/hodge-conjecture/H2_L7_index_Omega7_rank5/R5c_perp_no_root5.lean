/- R5 perp_no_root5 (Hodge table). Proof: Chair B (Claude Sonnet 5.5). Namespace Council = verbatim subset of #mwggdbvb-dl74i5 (Claude council · Results lead, Claude Opus 5.5).
PROVED here (kernel decide, no sorry): for n = 117, 351, 819, no x in Z^18 with x.Wm.v = 0 has x.Wm.x = 2. Steps: sc: v^perp = span of the council's 17 pb vectors; tie_G: their Gram; council nn2.
NOT shown: that Wm is the cited lattice W'; any Hodge content. -/
import Mathlib
open Matrix
def WL : List (List ℤ) := [[2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[-1,2,-1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,2,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,-1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,-1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,2,-1,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,-1,2,-1,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,-1,2,-1,0,-1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,2,-1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,-1,2,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,-1,0,0,2,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,2,-1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,-1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,-1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,2,0,1],[0,0,0,0,0,0,0,0,0,0,0,0,0,-1,0,0,2,0],[1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,4]]
def Wm : Matrix (Fin 18) (Fin 18) ℤ := Matrix.of fun i j => (WL.getD i []).getD j 0
def vL : List (List ℤ) := [[-25,-27,-17,-8,-13,-24,-25,-27,-17,-8,-13,-8,-17,-27,-25,-24,-13,24],[-50,-54,-34,-16,-26,-48,-50,-54,-34,-16,-26,-24,-49,-75,-65,-56,-37,48],[-100,-108,-68,-32,-52,-112,-130,-150,-98,-48,-74,-56,-113,-171,-145,-120,-85,96]]
/-- v for n = 117, 351, 819 (index 0, 1, 2), in W' coordinates. -/
def v (k : Fin 3) : Fin 18 → ℤ := fun j => (vL.getD k []).getD j 0

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
def gr (n : Nat) (E : List (Nat × Nat)) : M := (rg n).map fun i => (rg n).map fun j =>
  if i = j then 2 else if E.contains (i, j) || E.contains (j, i) then -1 else 0
def E : List (Nat × Nat) := (rg 3).flatMap fun b => [(0,1),(1,2),(2,3),(3,4),(2,5)].map fun (x, y) => (6*b+x, 6*b+y)
def B : M := ((rg 18).filter (· ≠ 0)).map (fun j => (rg 18).map fun i => if i = j then 3 else 0) ++ [[1,5,6,4,2,3,4,5,6,4,2,3,2,4,6,5,4,3]]
def W : M := (gm (gr 18 E) B).map (·.map (· / 9))
def pb (v : V) (k : Nat) : M := let g := W.map (dt · v)
  ((rg 18).filter (· ≠ k)).map fun j => (rg 18).map fun t => if t = j then 1 else if t = k then -g.getD j 0 * g.getD k 0 else 0
def CK (G : M) (b : Int) (P : V → Bool) : Bool :=
  vR (cR G) && chk G (cR G) (cD G) && (cR G).length == 17 && (go (cR G) (cD G * b)).all P
theorem nn2 (G : M) (h : CK G 2 (qf G · != 2) = true) (c : V) (hl : c.length = 17) : qf G c ≠ 2 :=
  fun h2 => by have := noval _ _ _ _ h c hl (by omega); simp [h2] at this
end Council
def toM (L : List (List ℤ)) (m n : ℕ) : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => (L.getD i []).getD j 0
def dimOK (L : List (List ℤ)) (m n : ℕ) : Bool := L.length == m && L.all (fun r => r.length == n)
def vl (k : Fin 3) : Council.V := vL.getD k []
def kk (k : Fin 3) : ℕ := [0, 11, 11].getD k 0
def Pm (k : Fin 3) : Matrix (Fin 17) (Fin 18) ℤ := toM (Council.pb (vl k) (kk k)) 17 18
def Qm (k : Fin 3) : Matrix (Fin 17) (Fin 18) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = ((List.range 18).filter (· ≠ kk k)).getD i 0 then 1 else 0
def Cm (k : Fin 3) : Matrix (Fin 18) (Fin 18) ℤ :=
  Matrix.of fun i j => if (i : ℕ) = kk k then (Wm *ᵥ v k) j else 0
theorem tie_W : toM Council.W 18 18 = Wm ∧ dimOK Council.W 18 18 = true := by decide +kernel
theorem tie_v : ∀ k : Fin 3, ((List.ofFn (v k)) = vl k) := by decide +kernel
theorem tie_P : ∀ k : Fin 3, dimOK (Council.pb (vl k) (kk k)) 17 18 = true := by decide +kernel
theorem tie_G : ∀ k : Fin 3, toM (Council.gm Council.W (Council.pb (vl k) (kk k))) 17 17 = Pm k * Wm * (Pm k)ᵀ := by decide +kernel
theorem sc : ∀ k : Fin 3, (Pm k)ᵀ * Qm k + Cm k = 1 := by decide +kernel
theorem chk3 : ∀ k : Fin 3, Council.CK (Council.gm Council.W (Council.pb (vl k) (kk k))) 2 (Council.qf (Council.gm Council.W (Council.pb (vl k) (kk k))) · != 2) = true := by decide +kernel

theorem g17 (y : Fin 17 → ℤ) (i : Fin 17) : (List.ofFn y).getD (i : ℕ) 0 = y i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp
theorem qfo (G : List (List ℤ)) (y : Fin 17 → ℤ) :
    Council.qf G (List.ofFn y) = y ⬝ᵥ (toM G 17 17 *ᵥ y) := by
  rw [Council.qf, Council.ps, List.length_ofFn]
  simp only [dotProduct, mulVec, toM, Matrix.of_apply, Finset.mul_sum, Finset.sum_range, g17]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
theorem qpb (k : Fin 3) (y : Fin 17 → ℤ) :
    ((Pm k)ᵀ *ᵥ y) ⬝ᵥ (Wm *ᵥ ((Pm k)ᵀ *ᵥ y)) = y ⬝ᵥ (((Pm k) * Wm * (Pm k)ᵀ) *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]
theorem Gk_no (k : Fin 3) (y : Fin 17 → ℤ) : y ⬝ᵥ (((Pm k) * Wm * (Pm k)ᵀ) *ᵥ y) ≠ 2 := by
  intro h
  have h2 : Council.qf (Council.gm Council.W (Council.pb (vl k) (kk k))) (List.ofFn y) = 2 := by
    rw [qfo, tie_G k, h]
  exact Council.nn2 _ (chk3 k) (List.ofFn y) (by simp) h2
/-- Clean form of "no norm-2 vector in v^⊥" (the council proved it only for the span of 17 vectors). -/
theorem perp_no_root5 (k : Fin 3) (x : Fin 18 → ℤ) (hx : x ⬝ᵥ (Wm *ᵥ v k) = 0) :
    x ⬝ᵥ (Wm *ᵥ x) ≠ 2 := by
  have hC : Cm k *ᵥ x = 0 := by
    funext i
    have hx' : (Wm *ᵥ v k) ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact hx
    by_cases h : (i : ℕ) = kk k
    · simpa [Cm, Matrix.mulVec, dotProduct, h] using hx'
    · simp [Cm, Matrix.mulVec, dotProduct, h]
  have hx2 : (Pm k)ᵀ *ᵥ (Qm k *ᵥ x) = x := by
    have h := congrArg (fun P => P *ᵥ x) (sc k)
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hC, add_zero, Matrix.one_mulVec] at h
    exact h
  rw [← hx2, qpb]
  exact Gk_no k _