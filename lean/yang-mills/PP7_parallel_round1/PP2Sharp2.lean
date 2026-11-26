import LongTable.PP2Sharp1
import LongTable.PP2Region

/-!
Yang-Mills table, Long Table. Claude council, target T2a (ε-uniform mass gap from a uniform
susceptibility bound, all λ ≥ 0), session 2 after PP2Sharp1: the ε-uniform boundary estimate.
Notation: B = B(x, r) the sup-ball (`physBall`), E(x, r) = Σ_{u∈B, v∉B} J_uv ⟨φ_xφ_u⟩_B
(`sh1_bdrySum`), ⟨·⟩_R the Dirichlet measure of a region R (`regionTwoPt`), χ ≤ K the uniform
susceptibility (ε² Σ_y ⟨φ_xφ_y⟩ ≤ K), ε = `spacing n`.

ROUTE ANALYSIS (decided on paper first).
(1) Free comparison with an effective mass (BFS local times / strong Gaussian domination for the
region measure). NOT a route from χ. Every site-by-site argument sees the bare coefficient
α = 4 + ε²(m₀² − 12λc), c ~ (2π)⁻¹ log ε⁻¹: the local-time weight gains e^{12λε²c} per unit of
local time and a walk in B spends ~ (r/ε)² there. The PP2SimonLieb3 contraction (weight e^{c'Στ})
is a fixed-ε, fixed-box positivity statement (its C₀ depends on ε) and yields no resolvent bound.
A comparison ⟨φ_xφ_u⟩_{B(x,l)} ≤ C ⟨φ_xφ_u⟩^{free, mass μ}_{B(x,l)} uniform in ε and l would be a
mass-gap statement by itself: recorded as `EffectiveMassDomination` ⟹
`clustering_of_effectiveMassDomination` (E ≤ 2C/cosh(κ_μ l) by `free_boundary_le`, no χ needed),
so it cannot be derived from χ by soft means.
(2) Smeared / nested boundaries. Any averaging which, after Griffiths II, bounds REGION two-point
functions by FULL ones loses the ε: ε-thin layers of nested regions are disjoint, Σ_j E(B_j) ≤
4 Σ_u ⟨φ_xφ_u⟩ ≤ 4K/ε², a physical window T needs T/ε layers, and a smooth cutoff of width w only
reweights (Σ_j w_j E_j ≤ 4 max w · K/ε² with Σ_j w_j ~ T/ε). The missing ε is the Dirichlet
suppression ⟨φ_xφ_u⟩_B = O(ε) near ∂B, invisible to every monotone comparison with full
correlations. (Same count with a coarea/level-set family of regions.)
(3) Double IBP on B (`dib_double_ibp_region'`, t(u) = Σ_{v∉B} J_uv, g = G_B t the free exit
potential): E = E⁰ − 12λε² Σ_z g(z) G_B(x,z) ⟨:φ_z²:⟩_B + 16λ² ⟨F_x F_g⟩_B. On a LARGE ball the
corrections are O(1), not small; bounding them needs interacting Wick-L² bounds for the region
measure (NelsonRegionHyp-type, unproven) and, for the λ² term, decay of the covariance of a Wick
cube smeared near x with one smeared near ∂B, i.e. clustering: circular. Fails on large balls for
large λ; it is the right tool only on THIN regions (see below).

THE ROUTE TAKEN: localise the boundary estimate to a strip of fixed physical width ρ. The ε loss
is a UV effect; the IR part is entirely carried by χ. For a side of B let D ⊂ B be the strip of
width ρ along it (t > r − ρ, t = ±(p_i − x_i) the signed coordinate normal to the side).
* Simon–Lieb INSIDE the ball measure (sub-region D, base point u on the side, x ∉ D as ρ ≤ r):
  ⟨φ_uφ_x⟩_B ≤ Σ_{w∈D, v'∉D} J_{wv'} ⟨φ_uφ_w⟩_D ⟨φ_{v'}φ_x⟩_B. Exchanging the sums, the side's
  boundary sum is Σ_{w, v'} J_{wv'} ⟨φ_{v'}φ_x⟩_B X_D(w), where X_D(w) is the crossing weight of
  the STRIP measure from w (adjacent to the inner edge of D) through the side. With X_D ≤ Cε/ρ
  and Griffiths II, the side sum is ≤ 4(Cε/ρ) Σ_{v' in the inner-edge row} ⟨φ_xφ_{v'}⟩: an ε-thin
  row, but now WITH the factor ε.
* Averaging over the radii r_j = ρ + jε (the rows are disjoint): Σ_{j<M} E(x, r_j) ≤
  16(Cε/ρ) Σ_v ⟨φ_xφ_v⟩ ≤ 16CK/(ρε); with M = T/ε, some r ≤ ρ + T has E ≤ 16CK/(ρT) ≤ 1/2 once
  T ≥ 32CK/ρ. No ε is lost. The finitely many coarse levels ε > ρ are covered by PP2Sharp1's
  fixed-level averaging (radius ≤ 8K/ε + 2 ≤ 8K/ρ + 2).
* Free field: X_D(w) ≤ 2ε/ρ (gambler's ruin; `exit_le` with the affine supersolution
  h = (t − (r − ρ − ε))/(ρ + ε): h ≥ 1 beyond the side, h ≥ 0 at every neighbour of D,
  h(w) ≤ 2ε/(ρ + ε)).
* Why the strip hypothesis is the natural, weakly coupled one for λ > 0: in a strip of width ρ
  the Dirichlet gap π²/ρ² dominates the Wick misordering shift −12λδ, δ ≈ (2π)⁻¹ log(1/(m₀ρ)), so
  the strip measure has a transverse gap and correlations along the strip decay at rate ~ π/ρ;
  hence a bound uniform in the strip length and position is expected for ρ ≤ ρ(λ, m₀), with
  C → 2 as λρ² log(1/ρ) → 0. Route (3) applied to D (t = the side bonds) gives
  X_D = X⁰_D − 12λε² Σ_z g G_D(w,z) ⟨:φ_z²:⟩_D + 16λ² ⟨F_w F_g⟩_D, where every term carries a factor
  ε because w is adjacent to ∂D (G_D(w,·) is itself Dirichlet-suppressed); what it needs is an
  ε-uniform L² bound for smeared Wick powers under thin-strip measures (a Nelson-type estimate at
  effective coupling λρ²·polylog, uniform in the length). Not checked in detail here.

DEFINITIONS.
* `sh2_t n k x i b p` = ±(p_i − x_i) (sign `sh2_sgn b`); `sh2_strip n k x r ρ i b` = the sites of
  B(x, r) with t > r − ρ; `sh2_wallExit … w` = Σ_{u∈D} Σ_{v∉B, t(v) > r} J_uv ⟨φ_wφ_u⟩_D.
* **`StripCrossing m₀ λ ρ C`**: for all n with ε ≤ ρ, k, x, r, sides (i, b), and every w ∈ D
  adjacent (bondJ ≠ 0) to a site of B ∖ D: `sh2_wallExit … w ≤ C ε/ρ`.
* **`RegionSimonLieb m₀ λ`**: for regions D ⊆ B, u ∈ D, any y:
  ⟨φ_uφ_y⟩_B ≤ ⟨φ_uφ_y⟩_D + Σ_{w∈D} Σ_{v∉D} J_wv ⟨φ_uφ_w⟩_D ⟨φ_vφ_y⟩_B.
* `sh2_sideSum` (boundary sum through one side), `sh2_row` (inner-edge row of the strip, weighted
  by the full two-point function), `EffectiveMassDomination m₀ λ μ C`.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* Geometry: `sh2_exists_side` (v ∉ B ⟹ beyond some side), `sh2_t_bond`, `sh2_t_le_supDist`,
  `sh2_regionTwoPt_symm`, `sh2_bdrySum_le_sides` (E ≤ Σ over the four sides).
* Free strip: `sh2_H_neighbours`, `sh2_H_nbr_ge`, `sh2_dirOp_h_nonneg` (dirOp h ≥ 0 on D, box
  boundary included) and **`sh2_stripCrossing_free`**: m₀ ≠ 0, ρ > 0 ⟹ StripCrossing m₀ 0 ρ 2.
* **`sh2_side_le`**: m₀ ≠ 0, λ ≥ 0, C ≥ 0, ρ > 0, RegionSimonLieb, StripCrossing ρ C, ε ≤ ρ ≤ r ⟹
  sh2_sideSum … x r i b ≤ 4 (C ε/ρ) Σ_v sh2_row … x r ρ i b v.
* `sh2_row_sum_le` (rows of the radii R + jε are disjoint), **`sh2_fine_radius`** (ε ≤ ρ: some
  r ∈ [ρ, ρ + ⌈32CK/ρ⌉ + 1] has E ≤ 1/2), `sh2_coarse_radius` (ε > ρ: r ≤ 8K/ρ + 2).
* **`varSmallBoundarySum_of_strip`**: VarSmallBoundarySum m₀ λ (ρ + ⌈32CK/ρ⌉ + 1 + 8K/ρ + 2) (1/2).
* **`clustering_of_uniformSusceptibility_of_strip`**: m₀ ≠ 0, λ ≥ 0, ρ > 0, C ≥ 0,
  UniformSusceptibility m₀ λ K, RegionSimonLieb m₀ λ, StripCrossing m₀ λ ρ C ⟹
  ∃ m > 0, FiniteCutoffClustering m₀ λ m (no DirichletSuppression).
* `clustering_free_of_strip` (λ = 0: only RegionSimonLieb and χ), `sh2_bdrySum_le_of_domination`,
  `clustering_of_effectiveMassDomination` (route (1) output ⟹ clustering, see above).

NOT FORMALIZED (what remains for T2a).
* `RegionSimonLieb` for λ ≥ 0: BFS Theorem 6.1 for the Dirichlet measure of B with sub-region D. It
  is the R5 step of PP2SimonLieb4 with the box pair matrix Jnn replaced by decJ B (couplings across
  ∂B removed) and the decoupling across ∂D; the abstract strong Gaussian domination of PP2SimonLieb3
  already holds for any ferromagnetic pair matrix. Mechanical but long (the box case,
  `simonLiebIneq'_holds`, took one session). At λ = 0 it is the resolvent identity.
* `StripCrossing` for λ > 0 (thin-strip, weak-coupling; see above). Proven only at λ = 0.
* `DirichletSuppression` itself is not proved; it is no longer needed.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset Matrix

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## Sides, strips and the strip crossing weight -/

/-- The sign attached to a Boolean: true ↦ 1, false ↦ −1. -/
def sh2_sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The signed coordinate of p relative to the centre x, in direction (i, b):
t(p) = ±(p_i − x_i). The side (i, b) of the ball B(x, r) is the line t = r. -/
def sh2_t (n k : ℕ) (x : DSite n k) (i : Fin 2) (b : Bool) (p : DSite n k) : ℝ :=
  sh2_sgn b * (dpos n k p i - dpos n k x i)

/-- The boundary strip of width ρ along the side (i, b) of B(x, r): the sites of the ball with
t > r − ρ. -/
def sh2_strip (n k : ℕ) (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) : Finset (DSite n k) :=
  (physBall n k x r).filter fun p => r - ρ < sh2_t n k x i b p

/-- The strip crossing weight from w: the exit weight of the STRIP measure (Dirichlet on the
complement of the strip) through the side (i, b) of the ball,
Σ_{u ∈ strip} Σ_{v ∉ B, t(v) > r} J_uv ⟨φ_w φ_u⟩_strip. -/
def sh2_wallExit (n k : ℕ) (m₀ lam : ℝ) (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool)
    (w : DSite n k) : ℝ :=
  ∑ u ∈ sh2_strip n k x r ρ i b, ∑ v ∈ (physBall n k x r)ᶜ,
    if r < sh2_t n k x i b v then
      bondJ n k u v * regionTwoPt n k m₀ lam (sh2_strip n k x r ρ i b) w u else 0

/-- **Thin-strip crossing bound** (the replacement of `DirichletSuppression`; a statement about
strips of the fixed physical width ρ only): from every site w of the strip that is adjacent to
the inner edge of the strip, the crossing weight of the strip measure through the outer side is
at most C ε / ρ. (Free field: C = 2, `sh2_stripCrossing_free`.) -/
def StripCrossing (m₀ lam ρ C : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k) (r : ℝ) (i : Fin 2) (b : Bool), spacing n ≤ ρ →
    ∀ w ∈ sh2_strip n k x r ρ i b, ∀ v ∈ physBall n k x r, v ∉ sh2_strip n k x r ρ i b →
      bondJ n k w v ≠ 0 → sh2_wallExit n k m₀ lam x r ρ i b w ≤ C * spacing n / ρ

/-- **Simon–Lieb for the region measures** (Lieb's inequality for the Dirichlet measure of a region
B with a sub-region D; BFS CMP 83, Theorem 6.1, which applies verbatim to the region measure;
the case of the box measure is `simonLiebIneq'_holds`). -/
def RegionSimonLieb (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B D : Finset (DSite n k)), D ⊆ B → ∀ u y : DSite n k, u ∈ D →
    regionTwoPt n k m₀ lam B u y ≤ regionTwoPt n k m₀ lam D u y +
      ∑ w ∈ D, ∑ v ∈ Dᶜ,
        bondJ n k w v * regionTwoPt n k m₀ lam D u w * regionTwoPt n k m₀ lam B v y

/-! ## Elementary geometry -/

theorem sh2_abs_sgn (b : Bool) : |sh2_sgn b| = 1 := by
  cases b <;> simp [sh2_sgn]

@[simp] theorem sh2_sgn_true : sh2_sgn true = 1 := rfl
@[simp] theorem sh2_sgn_false : sh2_sgn false = -1 := rfl

theorem sh2_coord_le_supDist (p q : Plane) (i : Fin 2) : |p i - q i| ≤ supDist p q := by
  unfold supDist
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem sh2_t_self (x : DSite n k) (i : Fin 2) (b : Bool) : sh2_t n k x i b x = 0 := by
  simp [sh2_t]

theorem sh2_abs_t_sub (x : DSite n k) (i : Fin 2) (b : Bool) (p q : DSite n k) :
    |sh2_t n k x i b p - sh2_t n k x i b q| = |dpos n k p i - dpos n k q i| := by
  unfold sh2_t
  rw [← mul_sub, abs_mul, sh2_abs_sgn, one_mul]
  congr 1; ring

theorem sh2_t_bond (x : DSite n k) (i : Fin 2) (b : Bool) {u v : DSite n k}
    (h : bondJ n k u v ≠ 0) : |sh2_t n k x i b u - sh2_t n k x i b v| ≤ spacing n := by
  rw [sh2_abs_t_sub]
  exact (sh2_coord_le_supDist _ _ i).trans (supDist_bondJ h)

theorem sh2_t_le_supDist (x : DSite n k) (i : Fin 2) (b : Bool) (p : DSite n k) :
    sh2_t n k x i b p ≤ supDist (dpos n k x) (dpos n k p) := by
  have h := sh2_abs_t_sub x i b p x
  rw [sh2_t_self, sub_zero] at h
  calc sh2_t n k x i b p ≤ |sh2_t n k x i b p| := le_abs_self _
    _ = |dpos n k x i - dpos n k p i| := by rw [h, abs_sub_comm]
    _ ≤ _ := sh2_coord_le_supDist _ _ i

/-- A site outside the ball lies beyond one of its four sides. -/
theorem sh2_exists_side {x v : DSite n k} {r : ℝ} (hv : v ∉ physBall n k x r) :
    ∃ i : Fin 2, ∃ b : Bool, r < sh2_t n k x i b v := by
  rw [mem_physBall, not_le] at hv
  unfold supDist at hv
  rcases lt_max_iff.mp hv with h | h
  · rcases lt_abs.mp h with h' | h'
    · exact ⟨0, false, by simp only [sh2_t, sh2_sgn_false]; linarith⟩
    · exact ⟨0, true, by simp only [sh2_t, sh2_sgn_true]; linarith⟩
  · rcases lt_abs.mp h with h' | h'
    · exact ⟨1, false, by simp only [sh2_t, sh2_sgn_false]; linarith⟩
    · exact ⟨1, true, by simp only [sh2_t, sh2_sgn_true]; linarith⟩

theorem sh2_mem_strip {x p : DSite n k} {r ρ : ℝ} {i : Fin 2} {b : Bool} :
    p ∈ sh2_strip n k x r ρ i b ↔ p ∈ physBall n k x r ∧ r - ρ < sh2_t n k x i b p := by
  simp [sh2_strip]

theorem sh2_strip_subset (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) :
    sh2_strip n k x r ρ i b ⊆ physBall n k x r := Finset.filter_subset _ _

theorem sh2_regionTwoPt_symm (m₀ lam : ℝ) (R : Finset (DSite n k)) (x y : DSite n k) :
    regionTwoPt n k m₀ lam R x y = regionTwoPt n k m₀ lam R y x := by
  unfold regionTwoPt
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  simp only; ring

/-! ## The free field: the strip crossing bound with C = 2 (gambler's ruin) -/

/-- The i-th physical coordinate of a lattice point q ∈ ℤ². -/
def sh2_qc (n k : ℕ) (i : Fin 2) (q : ℤ × ℤ) : ℝ :=
  spacing n * ((if i = 0 then q.1 else q.2 : ℤ) : ℝ) - boxL k / 2

theorem sh2_qc_site (i : Fin 2) (w : DSite n k) : sh2_qc n k i (site w) = dpos n k w i := by
  fin_cases i
  · simp [sh2_qc, site, dpos_zero]
  · simp [sh2_qc, site, dpos_one]

/-- The affine test function H(q) = (t(q) − a)/(ρ + ε), a = r − ρ − ε, on ℤ². -/
def sh2_H (n k : ℕ) (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) (q : ℤ × ℤ) : ℝ :=
  (sh2_sgn b * (sh2_qc n k i q - dpos n k x i) - (r - ρ - spacing n)) / (ρ + spacing n)

/-- Its restriction to the box. -/
def sh2_h (n k : ℕ) (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) : DField n k :=
  fun w => sh2_H n k x r ρ i b (site w)

theorem sh2_h_eq (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) (w : DSite n k) :
    sh2_h n k x r ρ i b w = (sh2_t n k x i b w - (r - ρ - spacing n)) / (ρ + spacing n) := by
  simp only [sh2_h, sh2_H, sh2_qc_site, sh2_t]

/-- The four neighbours: H is affine, so their sum is 4 H. -/
theorem sh2_H_neighbours (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) (s : ℤ × ℤ) :
    sh2_H n k x r ρ i b (s.1 - 1, s.2) + sh2_H n k x r ρ i b (s.1 + 1, s.2)
      + sh2_H n k x r ρ i b (s.1, s.2 - 1) + sh2_H n k x r ρ i b (s.1, s.2 + 1)
      = 4 * sh2_H n k x r ρ i b s := by
  fin_cases i <;>
  · simp only [sh2_H, sh2_qc]
    push_cast
    field_simp
    ring

/-- Each neighbour value differs from the centre value by at most ε/(ρ + ε). -/
theorem sh2_H_nbr_ge (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool) (hρ : 0 < ρ)
    (s : ℤ × ℤ) (q : ℤ × ℤ)
    (hq : q = (s.1 - 1, s.2) ∨ q = (s.1 + 1, s.2) ∨ q = (s.1, s.2 - 1) ∨ q = (s.1, s.2 + 1)) :
    sh2_H n k x r ρ i b s - spacing n / (ρ + spacing n) ≤ sh2_H n k x r ρ i b q := by
  have hε := spacing_pos n
  have hd : 0 < ρ + spacing n := by linarith
  have hdiff : sh2_qc n k i q - sh2_qc n k i s = spacing n *
      (((if i = 0 then q.1 else q.2) - (if i = 0 then s.1 else s.2) : ℤ) : ℝ) := by
    simp only [sh2_qc]; push_cast; ring
  have hd1 : |((((if i = 0 then q.1 else q.2) - (if i = 0 then s.1 else s.2) : ℤ)) : ℝ)| ≤ 1 := by
    rcases hq with rfl | rfl | rfl | rfl <;> fin_cases i <;> norm_num
  have key : |sh2_qc n k i q - sh2_qc n k i s| ≤ spacing n := by
    rw [hdiff, abs_mul, abs_of_pos hε]
    nlinarith [abs_nonneg ((((if i = 0 then q.1 else q.2) - (if i = 0 then s.1 else s.2) : ℤ)) : ℝ)]
  have hs := sh2_abs_sgn b
  unfold sh2_H
  rw [← sub_div, div_le_div_iff_of_pos_right hd]
  have h1 : |sh2_sgn b * (sh2_qc n k i q - sh2_qc n k i s)| ≤ spacing n := by
    rw [abs_mul, hs, one_mul]; exact key
  have h2 := (abs_le.mp h1).1
  have e : sh2_sgn b * (sh2_qc n k i q - dpos n k x i) =
      sh2_sgn b * (sh2_qc n k i s - dpos n k x i) +
        sh2_sgn b * (sh2_qc n k i q - sh2_qc n k i s) := by ring
  rw [e]; linarith

theorem sh2_ext_le {f : DField n k} {F : ℤ × ℤ → ℝ} (hf : ∀ w, f w = F (site w)) (q : ℤ × ℤ)
    (hq : 0 ≤ F q) : ext f q ≤ F q := by
  unfold ext
  split_ifs with h
  · apply le_of_eq
    rw [hf]
    show F (((q.1.toNat : ℕ) : ℤ), ((q.2.toNat : ℕ) : ℤ)) = F q
    rw [Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg h.2.2.1]
  · exact hq

/-- **The affine supersolution:** dirOp h ≥ 0 on the strip. -/
theorem sh2_dirOp_h_nonneg (m₀ : ℝ) (x : DSite n k) {r ρ : ℝ} (i : Fin 2) (b : Bool)
    (hρ : 0 < ρ) {w : DSite n k} (hw : w ∈ sh2_strip n k x r ρ i b) :
    0 ≤ (dirOp n k m₀ *ᵥ sh2_h n k x r ρ i b) w := by
  rw [dirOp_mulVec_apply]
  have hε := spacing_pos n
  have hd : 0 < ρ + spacing n := by linarith
  set H := sh2_H n k x r ρ i b with hHdef
  have hw' := (sh2_mem_strip.mp hw).2
  have hHw : sh2_h n k x r ρ i b w = H (site w) := rfl
  have hHpos : spacing n / (ρ + spacing n) < H (site w) := by
    rw [← hHw, sh2_h_eq]
    exact div_lt_div_of_pos_right (by linarith) hd
  have hfH : ∀ z, sh2_h n k x r ρ i b z = H (site z) := fun z => rfl
  have hnb : ∀ q, (q = ((site w).1 - 1, (site w).2) ∨ q = ((site w).1 + 1, (site w).2) ∨
      q = ((site w).1, (site w).2 - 1) ∨ q = ((site w).1, (site w).2 + 1)) →
      ext (sh2_h n k x r ρ i b) q ≤ H q := fun q hq =>
    sh2_ext_le hfH q (by linarith [sh2_H_nbr_ge x r ρ i b hρ (site w) q hq])
  have e1 := hnb _ (Or.inl rfl)
  have e2 := hnb _ (Or.inr (Or.inl rfl))
  have e3 := hnb _ (Or.inr (Or.inr (Or.inl rfl)))
  have e4 := hnb _ (Or.inr (Or.inr (Or.inr rfl)))
  have hs := sh2_H_neighbours x r ρ i b (site w)
  rw [← hHdef] at hs
  rw [hHw]
  have hP : 0 < (spacing n ^ 2)⁻¹ := inv_pos.mpr (pow_pos hε 2)
  have hin : 0 ≤ (2 * H (site w) - ext (sh2_h n k x r ρ i b) ((site w).1 - 1, (site w).2)
        - ext (sh2_h n k x r ρ i b) ((site w).1 + 1, (site w).2))
      + (2 * H (site w) - ext (sh2_h n k x r ρ i b) ((site w).1, (site w).2 - 1)
        - ext (sh2_h n k x r ρ i b) ((site w).1, (site w).2 + 1)) := by linarith
  have hm : 0 ≤ m₀ ^ 2 * H (site w) :=
    mul_nonneg (sq_nonneg _) (le_trans (div_nonneg hε.le hd.le) hHpos.le)
  exact add_nonneg (mul_nonneg hP.le hin) hm

/-- **The free strip crossing bound** (gambler's ruin): at λ = 0, from a strip site w adjacent to
the inner edge, the crossing weight through the outer side is at most 2ε/ρ. -/
theorem sh2_stripCrossing_free {m₀ ρ : ℝ} (hm : m₀ ≠ 0) (hρ : 0 < ρ) :
    StripCrossing m₀ 0 ρ 2 := by
  intro n k x r i b _ w hw v' hv'B hv'D hJ
  have hε := spacing_pos n
  have hd : 0 < ρ + spacing n := by linarith
  set B := physBall n k x r with hBdef
  set D := sh2_strip n k x r ρ i b with hDdef
  set h := sh2_h n k x r ρ i b with hhdef
  set t := sh2_t n k x i b with htdef
  have hex := exit_le hm D h (fun w' hw' => sh2_dirOp_h_nonneg m₀ x i b hρ hw') ⟨w, hw⟩
  have hht : ∀ z, h z = (t z - (r - ρ - spacing n)) / (ρ + spacing n) := fun z =>
    sh2_h_eq x r ρ i b z
  -- h ≥ 0 at every neighbour of the strip, h ≥ 1 beyond the side
  have hnn : ∀ u ∈ D, ∀ v, bondJ n k u v ≠ 0 → 0 ≤ h v := by
    intro u hu v huv
    have h1 := (sh2_mem_strip.mp hu).2
    have h2 := (abs_le.mp (sh2_t_bond x i b huv)).2
    rw [hht]; exact div_nonneg (by linarith) hd.le
  have hge : ∀ v, r < t v → 1 ≤ h v := by
    intro v hv
    rw [hht, le_div_iff₀ hd]; linarith
  -- h(w) ≤ 2ε/ρ
  have hwle : h w ≤ 2 * spacing n / ρ := by
    have h1 : ¬ (r - ρ < t v') := fun hc => hv'D (sh2_mem_strip.mpr ⟨hv'B, hc⟩)
    have h2 := (abs_le.mp (sh2_t_bond x i b hJ)).2
    rw [hht]
    calc (t w - (r - ρ - spacing n)) / (ρ + spacing n) ≤ (2 * spacing n) / (ρ + spacing n) :=
          div_le_div_of_nonneg_right (by push Not at h1; linarith) hd.le
      _ ≤ 2 * spacing n / ρ := div_le_div_of_nonneg_left (by positivity) hρ (by linarith)
  refine le_trans ?_ (hwle.trans_eq' rfl)
  refine le_trans ?_ hex
  unfold sh2_wallExit
  rw [← hDdef, ← hBdef, ← Finset.sum_coe_sort D]
  refine Finset.sum_le_sum fun u _ => ?_
  have hGu : 0 ≤ (spacing n ^ 2)⁻¹ * regionGreen n k m₀ D ⟨w, hw⟩ u :=
    mul_nonneg (inv_nonneg.mpr (by positivity)) (rg_regionGreen_nonneg hm D _ u)
  have hfree : regionTwoPt n k m₀ 0 D w u =
      (spacing n ^ 2)⁻¹ * regionGreen n k m₀ D ⟨w, hw⟩ u := regionTwoPt_free hm D ⟨w, hw⟩ u
  have hBD : Bᶜ ⊆ Dᶜ := Finset.compl_subset_compl.mpr (sh2_strip_subset x r ρ i b)
  have hterm : ∀ v ∈ Dᶜ, 0 ≤ bondJ n k u v *
      ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ D ⟨w, hw⟩ u) * h v := by
    intro v hv
    have huv : (u : DSite n k) ≠ v := by
      rintro h'; rw [← h'] at hv; exact (Finset.mem_compl.mp hv) u.2
    by_cases hJ0 : bondJ n k u v = 0
    · rw [hJ0, zero_mul, zero_mul]
    · exact mul_nonneg (mul_nonneg (bondJ_nonneg huv) hGu) (hnn u u.2 v hJ0)
  calc ∑ v ∈ Bᶜ, (if r < t v then bondJ n k u v * regionTwoPt n k m₀ 0 D w u else 0)
      ≤ ∑ v ∈ Bᶜ, bondJ n k u v *
          ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ D ⟨w, hw⟩ u) * h v := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [hfree]
        split_ifs with hr
        · have huv : (u : DSite n k) ≠ v := by
            rintro h'; rw [← h'] at hv; exact (Finset.mem_compl.mp hv) (sh2_strip_subset x r ρ i b u.2)
          have := mul_nonneg (bondJ_nonneg huv) hGu
          nlinarith [hge v hr]
        · exact hterm v (hBD hv)
    _ ≤ ∑ v ∈ Dᶜ, bondJ n k u v *
          ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ D ⟨w, hw⟩ u) * h v :=
        Finset.sum_le_sum_of_subset_of_nonneg hBD fun v hv _ => hterm v hv

/-! ## Splitting the boundary sum over the four sides -/

/-- The part of the Simon–Lieb boundary sum of B(x, r) through the side (i, b). -/
def sh2_sideSum (n k : ℕ) (m₀ lam : ℝ) (x : DSite n k) (r : ℝ) (i : Fin 2) (b : Bool) : ℝ :=
  ∑ u ∈ physBall n k x r, ∑ v ∈ (physBall n k x r)ᶜ,
    if r < sh2_t n k x i b v then
      bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x r) x u else 0

theorem sh2_bdrySum_le_sides (m₀ lam : ℝ) (x : DSite n k) (r : ℝ) :
    sh1_bdrySum n k m₀ lam x r ≤ ∑ p : Fin 2 × Bool, sh2_sideSum n k m₀ lam x r p.1 p.2 := by
  set B := physBall n k x r with hBdef
  set F : DSite n k → DSite n k → Fin 2 × Bool → ℝ := fun u v p =>
    if r < sh2_t n k x p.1 p.2 v then bondJ n k u v * regionTwoPt n k m₀ lam B x u else 0
    with hF
  have e : ∑ p : Fin 2 × Bool, sh2_sideSum n k m₀ lam x r p.1 p.2 =
      ∑ u ∈ B, ∑ v ∈ Bᶜ, ∑ p : Fin 2 × Bool, F u v p := by
    unfold sh2_sideSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  rw [e]
  unfold sh1_bdrySum
  refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => ?_
  have hvn : v ∉ B := Finset.mem_compl.mp hv
  have huv : u ≠ v := by rintro rfl; exact hvn hu
  have h0 : 0 ≤ bondJ n k u v * regionTwoPt n k m₀ lam B x u :=
    mul_nonneg (bondJ_nonneg huv) (regionGriffithsI_holds m₀ lam n k _ x u)
  obtain ⟨i, b, hib⟩ := sh2_exists_side hvn
  have hnn : ∀ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), 0 ≤ F u v p := fun p _ => by
    simp only [hF]; split_ifs
    · exact h0
    · exact le_rfl
  have := Finset.single_le_sum hnn (Finset.mem_univ (i, b))
  simp only [hF, hib, ite_true] at this
  exact this

/-! ## The side estimate: Simon–Lieb inside the ball + the strip crossing bound -/

/-- The inner-edge row of the strip of width ρ (r − ρ − ε < t ≤ r − ρ), weighted by the full
two-point function. -/
def sh2_row (n k : ℕ) (m₀ lam : ℝ) (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool)
    (v : DSite n k) : ℝ :=
  if sh2_t n k x i b v ≤ r - ρ ∧ ¬ (sh2_t n k x i b v + spacing n ≤ r - ρ) then
    twoPt n k m₀ lam x v else 0

theorem sh2_row_nonneg (m₀ lam : ℝ) (x : DSite n k) (r ρ : ℝ) (i : Fin 2) (b : Bool)
    (v : DSite n k) : 0 ≤ sh2_row n k m₀ lam x r ρ i b v := by
  unfold sh2_row; split_ifs
  · exact twoPt_nonneg m₀ lam x v
  · exact le_rfl

/-- **The side estimate.** Region Simon–Lieb for the ball measure with the boundary strip D of
width ρ as sub-region, then the strip crossing bound: the boundary sum through one side is at most
4 C ε/ρ times the full two-point function summed over the inner-edge row of the strip. -/
theorem sh2_side_le {m₀ lam ρ C : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hRSL : RegionSimonLieb m₀ lam) (hS : StripCrossing m₀ lam ρ C)
    (x : DSite n k) {r : ℝ} (hερ : spacing n ≤ ρ) (hρr : ρ ≤ r) (i : Fin 2) (b : Bool) :
    sh2_sideSum n k m₀ lam x r i b ≤
      4 * (C * spacing n / ρ) * ∑ v, sh2_row n k m₀ lam x r ρ i b v := by
  set B := physBall n k x r with hBdef
  set D := sh2_strip n k x r ρ i b with hDdef
  set t := sh2_t n k x i b with htdef
  set TB := regionTwoPt n k m₀ lam B with hTB
  set TD := regionTwoPt n k m₀ lam D with hTD
  have hε := spacing_pos n
  have hDB : D ⊆ B := sh2_strip_subset x r ρ i b
  have hxD : x ∉ D := by
    intro h; have := (sh2_mem_strip.mp h).2; rw [sh2_t_self] at this; linarith
  have hGI := regionGriffithsI_holds m₀ lam
  set Φ : DSite n k → ℝ := fun u => ∑ w ∈ D, ∑ v' ∈ Dᶜ, bondJ n k w v' * TD u w * TB v' x
    with hΦ
  have hcross : ∀ u v, r < t v → bondJ n k u v ≠ 0 → r - ρ < t u := by
    intro u v hv hJ
    have := (abs_le.mp (sh2_t_bond x i b hJ)).1
    linarith
  have hSL : ∀ u ∈ D, TB x u ≤ Φ u := by
    intro u hu
    have h1 := hRSL n k B D hDB u x hu
    rw [regionTwoPt_out m₀ lam D u hxD, zero_add] at h1
    rw [hTB, sh2_regionTwoPt_symm]; exact h1
  -- step 1: only bonds leaving from the strip contribute; apply Simon–Lieb
  have step1 : sh2_sideSum n k m₀ lam x r i b ≤
      ∑ u ∈ D, ∑ v ∈ Bᶜ, (if r < t v then bondJ n k u v * Φ u else 0) := by
    unfold sh2_sideSum
    rw [← hBdef, show D = B.filter (fun u => r - ρ < t u) from rfl, Finset.sum_filter]
    refine Finset.sum_le_sum fun u hu => ?_
    split_ifs with hu'
    · refine Finset.sum_le_sum fun v hv => ?_
      have huv : u ≠ v := by rintro rfl; exact (Finset.mem_compl.mp hv) hu
      split_ifs with hr
      · exact mul_le_mul_of_nonneg_left (hSL u (sh2_mem_strip.mpr ⟨hu, hu'⟩)) (bondJ_nonneg huv)
      · exact le_rfl
    · refine le_of_eq (Finset.sum_eq_zero fun v _ => ?_)
      split_ifs with hr
      · by_cases hJ : bondJ n k u v = 0
        · rw [hJ, zero_mul]
        · exact absurd (hcross u v hr hJ) hu'
      · rfl
  -- step 2: exchange the order of summation
  set G : DSite n k → DSite n k → DSite n k → DSite n k → ℝ := fun u v w v' =>
    (if r < t v then bondJ n k u v * TD w u else 0) * (bondJ n k w v' * TB v' x) with hG
  have step2 : ∑ u ∈ D, ∑ v ∈ Bᶜ, (if r < t v then bondJ n k u v * Φ u else 0) =
      ∑ w ∈ D, ∑ v' ∈ Dᶜ, sh2_wallExit n k m₀ lam x r ρ i b w * (bondJ n k w v' * TB v' x) := by
    have e1 : ∀ u v, (if r < t v then bondJ n k u v * Φ u else 0) =
        ∑ w ∈ D, ∑ v' ∈ Dᶜ, G u v w v' := by
      intro u v
      simp only [hG]
      split_ifs
      · rw [hΦ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v' _ => ?_
        rw [hTD, sh2_regionTwoPt_symm m₀ lam D w u]; ring
      · simp
    calc ∑ u ∈ D, ∑ v ∈ Bᶜ, (if r < t v then bondJ n k u v * Φ u else 0)
        = ∑ u ∈ D, ∑ v ∈ Bᶜ, ∑ w ∈ D, ∑ v' ∈ Dᶜ, G u v w v' :=
          Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => e1 u v
      _ = ∑ u ∈ D, ∑ w ∈ D, ∑ v ∈ Bᶜ, ∑ v' ∈ Dᶜ, G u v w v' :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ w ∈ D, ∑ u ∈ D, ∑ v ∈ Bᶜ, ∑ v' ∈ Dᶜ, G u v w v' := Finset.sum_comm
      _ = ∑ w ∈ D, ∑ v' ∈ Dᶜ, ∑ u ∈ D, ∑ v ∈ Bᶜ, G u v w v' := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v' _ => ?_
          rw [sh2_wallExit, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_mul]
  -- step 3: the strip crossing bound
  have step3 : ∑ w ∈ D, ∑ v' ∈ Dᶜ,
      sh2_wallExit n k m₀ lam x r ρ i b w * (bondJ n k w v' * TB v' x)
      ≤ ∑ w ∈ D, ∑ v' ∈ Dᶜ, (C * spacing n / ρ) * (bondJ n k w v' * TB v' x) := by
    refine Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun v' hv' => ?_
    have hv'D : v' ∉ D := Finset.mem_compl.mp hv'
    have hwv : w ≠ v' := by rintro rfl; exact hv'D hw
    by_cases hv'B : v' ∈ B
    · by_cases hJ : bondJ n k w v' = 0
      · rw [hJ]; simp
      · exact mul_le_mul_of_nonneg_right (hS n k x r i b hερ w hw v' hv'B hv'D hJ)
          (mul_nonneg (bondJ_nonneg hwv) (hGI n k B v' x))
    · rw [hTB, sh1_regionTwoPt_out_left m₀ lam B hv'B x]; simp
  -- step 4: only the inner-edge row of the strip is reached
  have hc0 : 0 ≤ C * spacing n / ρ := by positivity
  have step4 : ∑ w ∈ D, ∑ v' ∈ Dᶜ, (C * spacing n / ρ) * (bondJ n k w v' * TB v' x)
      ≤ ∑ v', (C * spacing n / ρ) * (4 * sh2_row n k m₀ lam x r ρ i b v') := by
    rw [Finset.sum_comm]
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Dᶜ)
      fun v' _ _ => mul_nonneg hc0 (by linarith [sh2_row_nonneg m₀ lam x r ρ i b v']))
    refine Finset.sum_le_sum fun v' hv' => ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    have hv'D : v' ∉ D := Finset.mem_compl.mp hv'
    rw [← Finset.sum_mul]
    have hrow0 := sh2_row_nonneg m₀ lam x r ρ i b v'
    by_cases hv'B : v' ∈ B
    · have ht' : t v' ≤ r - ρ := by
        by_contra hc; push Not at hc; exact hv'D (sh2_mem_strip.mpr ⟨hv'B, hc⟩)
      by_cases hband : ¬ (t v' + spacing n ≤ r - ρ)
      · have hrow : sh2_row n k m₀ lam x r ρ i b v' = twoPt n k m₀ lam x v' := by
          unfold sh2_row
          split_ifs with hcond
          · rfl
          · exact absurd ⟨ht', hband⟩ hcond
        rw [hrow]
        have hJs : ∑ w ∈ D, bondJ n k w v' ≤ 4 := by
          calc ∑ w ∈ D, bondJ n k w v' = ∑ w ∈ D, Jsym n k v' w :=
                Finset.sum_congr rfl fun w hw => by
                  have : v' ≠ w := by rintro rfl; exact hv'D hw
                  rw [Jsym_eq_bondJ this, bondJ_symm]
            _ ≤ ∑ w, Jsym n k v' w :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  fun w _ _ => sh1_Jsym_nonneg v' w
            _ ≤ 4 := Jsym_row_le v'
        have hT : TB v' x ≤ twoPt n k m₀ lam x v' := by
          rw [hTB, sh2_regionTwoPt_symm]; exact sh1_regionTwoPt_le_twoPt hm hlam B x v'
        exact mul_le_mul hJs hT (hGI n k B v' x) (by norm_num)
      · push Not at hband
        have hzero : ∑ w ∈ D, bondJ n k w v' = 0 := Finset.sum_eq_zero fun w hw => by
          by_contra hJ
          have h1 := (sh2_mem_strip.mp hw).2
          have h2 := (abs_le.mp (sh2_t_bond x i b hJ)).2
          linarith
        rw [hzero, zero_mul]; linarith
    · rw [hTB, sh1_regionTwoPt_out_left m₀ lam B hv'B x, mul_zero]; linarith
  calc sh2_sideSum n k m₀ lam x r i b ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step3
    _ ≤ _ := step4
    _ = 4 * (C * spacing n / ρ) * ∑ v, sh2_row n k m₀ lam x r ρ i b v := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring

/-! ## Averaging over radii and the ε-uniform small boundary sum -/

/-- The inner-edge rows of the strips of the balls of radii R + jε (j < M) are disjoint. -/
theorem sh2_row_sum_le (m₀ lam R ρ : ℝ) (x : DSite n k) (i : Fin 2) (b : Bool) (M : ℕ)
    (v : DSite n k) :
    ∑ j ∈ Finset.range M, sh2_row n k m₀ lam x (R + j * spacing n) ρ i b v ≤
      twoPt n k m₀ lam x v := by
  have hc := sh1_count_le_one (R₀ := R - ρ) (du := sh2_t n k x i b v)
    (dv := sh2_t n k x i b v + spacing n) (spacing_pos n) le_rfl M
  have e : ∀ j : ℕ, sh2_row n k m₀ lam x (R + j * spacing n) ρ i b v =
      (if sh2_t n k x i b v ≤ R - ρ + j * spacing n ∧
          ¬ sh2_t n k x i b v + spacing n ≤ R - ρ + j * spacing n then (1 : ℝ) else 0) *
        twoPt n k m₀ lam x v := by
    intro j
    unfold sh2_row
    rw [show R + j * spacing n - ρ = R - ρ + j * spacing n by ring]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.sum_mul]
  calc _ ≤ 1 * twoPt n k m₀ lam x v :=
        mul_le_mul_of_nonneg_right hc (twoPt_nonneg m₀ lam x v)
    _ = _ := one_mul _

/-- **Fine levels (ε ≤ ρ).** Some radius r ∈ [ρ, ρ + T], T = ⌈32CK/ρ⌉ + 1, has boundary sum
≤ 1/2, uniformly in n, k, x. -/
theorem sh2_fine_radius {m₀ lam ρ C K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hRSL : RegionSimonLieb m₀ lam) (hS : StripCrossing m₀ lam ρ C)
    (hK : UniformSusceptibility m₀ lam K) (n k : ℕ) (x : DSite n k) (hερ : spacing n ≤ ρ) :
    ∃ r : ℝ, ρ ≤ r ∧ r ≤ ρ + ((⌈32 * C * K / ρ⌉₊ + 1 : ℕ) : ℝ) ∧
      sh1_bdrySum n k m₀ lam x r ≤ 1 / 2 := by
  have hK0 := sh1_K_nonneg hK
  set T : ℕ := ⌈32 * C * K / ρ⌉₊ + 1 with hTdef
  have hε := spacing_pos n
  have hε2 : spacing n * 2 ^ n = 1 := by unfold spacing; rw [← mul_pow]; norm_num
  have hT32 : 32 * C * K / ρ ≤ T := by
    rw [hTdef]; push_cast; linarith [Nat.le_ceil (32 * C * K / ρ)]
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈32 * C * K / ρ⌉₊]
  set M : ℕ := T * 2 ^ n with hMdef
  have hM : 0 < M := by rw [hMdef]; positivity
  have hMr : (M : ℝ) * spacing n = T := by
    rw [hMdef]; push_cast; rw [mul_assoc, mul_comm ((2 : ℝ) ^ n), hε2, mul_one]
  set S : ℝ := ∑ v, twoPt n k m₀ lam x v with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun v _ => twoPt_nonneg m₀ lam x v
  have hχ : spacing n ^ 2 * S ≤ K := by
    refine le_trans (le_of_eq ?_) (hK n k x)
    congr 1
    exact Finset.sum_congr rfl fun u _ => (abs_of_nonneg (twoPt_nonneg m₀ lam x u)).symm
  set c : ℝ := 4 * (C * spacing n / ρ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hsum : ∑ j ∈ Finset.range M, sh1_bdrySum n k m₀ lam x (ρ + j * spacing n) ≤
      4 * c * S := by
    calc ∑ j ∈ Finset.range M, sh1_bdrySum n k m₀ lam x (ρ + j * spacing n)
        ≤ ∑ j ∈ Finset.range M, c * ∑ p : Fin 2 × Bool,
            ∑ v, sh2_row n k m₀ lam x (ρ + j * spacing n) ρ p.1 p.2 v := by
          refine Finset.sum_le_sum fun j _ => (sh2_bdrySum_le_sides m₀ lam x _).trans ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun p _ => sh2_side_le hm hlam hC hρ hRSL hS x hερ
            (by nlinarith [Nat.cast_nonneg (α := ℝ) j]) p.1 p.2
      _ = c * ∑ p : Fin 2 × Bool, ∑ v,
            ∑ j ∈ Finset.range M, sh2_row n k m₀ lam x (ρ + j * spacing n) ρ p.1 p.2 v := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
      _ ≤ c * ∑ _p : Fin 2 × Bool, S := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ =>
            Finset.sum_le_sum fun v _ => sh2_row_sum_le m₀ lam ρ ρ x p.1 p.2 M v) hc0
      _ = 4 * c * S := by
          rw [Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
          push_cast; ring
  have hne : (Finset.range M).Nonempty := Finset.nonempty_range_iff.mpr hM.ne'
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum' : ∑ j ∈ Finset.range M, sh1_bdrySum n k m₀ lam x (ρ + j * spacing n) ≤
      ∑ _j ∈ Finset.range M, 4 * c * S / M := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hMpos.ne']
    exact hsum
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le hne hsum'
  have hjM := Finset.mem_range.mp hj
  refine ⟨ρ + j * spacing n, by nlinarith [Nat.cast_nonneg (α := ℝ) j], ?_, hle.trans ?_⟩
  · have : (j : ℝ) * spacing n ≤ T := by
      rw [← hMr]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjM.le) hε.le
    linarith
  · have hTpos : (0 : ℝ) < T := by linarith
    have hMe : (M : ℝ) = T / spacing n := by rw [← hMr]; field_simp
    have e : 4 * c * S / M = 16 * C * (spacing n ^ 2 * S) / (ρ * T) := by
      rw [hMe, hc]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : 32 * C * K ≤ T * ρ := by rwa [div_le_iff₀ hρ] at hT32
    nlinarith [mul_le_mul_of_nonneg_left hχ (by positivity : (0 : ℝ) ≤ 16 * C)]

/-- **Coarse levels (ε > ρ):** the fixed-spacing averaging of PP2Sharp1 already gives a radius
≤ 8K/ρ + 2 (there are finitely many such levels, and 1/ε < 1/ρ on them). -/
theorem sh2_coarse_radius {m₀ lam ρ K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam) (hρ : 0 < ρ)
    (hK : UniformSusceptibility m₀ lam K) (n k : ℕ) (x : DSite n k) (hερ : ρ < spacing n) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 8 * K / ρ + 2 ∧ sh1_bdrySum n k m₀ lam x r ≤ 1 / 2 := by
  obtain ⟨r, hr0, hrL, hr⟩ := sh1_level_smallBoundarySum hm hlam n (hK n) k x
  refine ⟨r, hr0, hrL.trans ?_, hr⟩
  have hK0 := sh1_K_nonneg hK
  have hε := spacing_pos n
  have hε1 := spacing_le_one n
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8 * K / spacing n ^ 2 by positivity)
  push_cast
  have e : (8 * K / spacing n ^ 2) * spacing n = 8 * K / spacing n := by field_simp
  have h1 : 8 * K / spacing n ≤ 8 * K / ρ :=
    div_le_div_of_nonneg_left (by positivity) hρ hερ.le
  calc ((⌈8 * K / spacing n ^ 2⌉₊ : ℝ) + 1) * spacing n
      ≤ (8 * K / spacing n ^ 2 + 2) * spacing n :=
        mul_le_mul_of_nonneg_right (by linarith) hε.le
    _ = 8 * K / spacing n + 2 * spacing n := by rw [add_mul, e]
    _ ≤ _ := by linarith

/-- **ε-uniform small boundary sum** from the uniform susceptibility, region Simon–Lieb and the
thin-strip crossing bound (any width ρ > 0): γ = 1/2, radius ≤ ρ + ⌈32CK/ρ⌉ + 1 + 8K/ρ + 2. -/
theorem varSmallBoundarySum_of_strip {m₀ lam ρ C K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hK : UniformSusceptibility m₀ lam K)
    (hRSL : RegionSimonLieb m₀ lam) (hS : StripCrossing m₀ lam ρ C) :
    VarSmallBoundarySum m₀ lam
      (ρ + ((⌈32 * C * K / ρ⌉₊ + 1 : ℕ) : ℝ) + (8 * K / ρ + 2)) (1 / 2) := by
  intro n k x
  have hK0 := sh1_K_nonneg hK
  have hL1 : 0 ≤ 8 * K / ρ + 2 := by positivity
  have hL2 : 0 ≤ ((⌈32 * C * K / ρ⌉₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hερ : spacing n ≤ ρ
  · obtain ⟨r, h1, h2, h3⟩ := sh2_fine_radius hm hlam hC hρ hRSL hS hK n k x hερ
    exact ⟨r, by linarith, by linarith, h3⟩
  · push Not at hερ
    obtain ⟨r, h1, h2, h3⟩ := sh2_coarse_radius hm hlam hρ hK n k x hερ
    exact ⟨r, h1, by linarith, h3⟩

/-- **Uniform susceptibility + region Simon–Lieb + thin-strip crossing ⟹ ε-uniform exponential
clustering**, for every λ ≥ 0 (m₀ ≠ 0). No `DirichletSuppression` is assumed. -/
theorem clustering_of_uniformSusceptibility_of_strip {m₀ lam ρ C K : ℝ} (hm : m₀ ≠ 0)
    (hlam : 0 ≤ lam) (hρ : 0 < ρ) (hC : 0 ≤ C) (hK : UniformSusceptibility m₀ lam K)
    (hRSL : RegionSimonLieb m₀ lam) (hS : StripCrossing m₀ lam ρ C) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m := by
  have hK0 := sh1_K_nonneg hK
  have hL : 0 ≤ ρ + ((⌈32 * C * K / ρ⌉₊ + 1 : ℕ) : ℝ) + (8 * K / ρ + 2) := by positivity
  exact clustering_of_varSmallBoundarySum hm hlam hL (by norm_num) (by norm_num)
    (varSmallBoundarySum_of_strip hm hlam hρ hC hK hRSL hS) hK

/-- Sanity check at λ = 0 of the strip route: the free field satisfies the strip hypothesis
(C = 2), so for it the route needs only region Simon–Lieb and the susceptibility. -/
theorem clustering_free_of_strip {m₀ K : ℝ} (hm : m₀ ≠ 0) (hK : UniformSusceptibility m₀ 0 K)
    (hRSL : RegionSimonLieb m₀ 0) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ 0 m :=
  clustering_of_uniformSusceptibility_of_strip hm le_rfl one_pos (by norm_num) hK hRSL
    (sh2_stripCrossing_free hm one_pos)

/-! ## Route (1), for the record: an effective-mass comparison is itself a gap statement -/

/-- Comparison of the interacting Dirichlet-ball two-point function with the FREE Dirichlet-ball
two-point function of some mass μ, uniformly in n, k, x and the radius l. -/
def EffectiveMassDomination (m₀ lam μ C : ℝ) : Prop :=
  ∀ (n k : ℕ) (x : DSite n k) (l : ℝ), 0 ≤ l → ∀ u ∈ physBall n k x l,
    regionTwoPt n k m₀ lam (physBall n k x l) x u ≤
      C * regionTwoPt n k μ 0 (physBall n k x l) x u

theorem sh2_bdrySum_le_of_domination {m₀ lam μ C : ℝ} (hμ : μ ≠ 0) (hC : 0 ≤ C)
    (hD : EffectiveMassDomination m₀ lam μ C) {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) :
    sh1_bdrySum n k m₀ lam x l ≤ C * (2 / Real.cosh (rg_kappa μ * l)) := by
  have hx := rg_mem_physBall_self (n := n) (k := k) hl x
  have hfree := free_boundary_le hμ hl n k x
  unfold sh1_bdrySum
  calc ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
        bondJ n k u v * regionTwoPt n k m₀ lam (physBall n k x l) x u
      ≤ ∑ u ∈ physBall n k x l, ∑ v ∈ (physBall n k x l)ᶜ,
        C * (bondJ n k u v * regionTwoPt n k μ 0 (physBall n k x l) x u) := by
        refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => ?_
        have huv : u ≠ v := by rintro rfl; exact (Finset.mem_compl.mp hv) hu
        have := mul_le_mul_of_nonneg_left (hD n k x l hl u hu) (bondJ_nonneg huv)
        rw [mul_left_comm C]; exact this
    _ = C * ∑ u : {z // z ∈ physBall n k x l}, ∑ v ∈ (physBall n k x l)ᶜ,
          bondJ n k u v * ((spacing n ^ 2)⁻¹ *
            regionGreen n k μ (physBall n k x l) ⟨x, hx⟩ u) := by
        rw [Finset.mul_sum, ← Finset.sum_coe_sort (physBall n k x l)]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [regionTwoPt_free hμ _ ⟨x, hx⟩ u]
    _ ≤ C * (2 / Real.cosh (rg_kappa μ * l)) := mul_le_mul_of_nonneg_left hfree hC

/-- An `EffectiveMassDomination` (with μ ≠ 0) gives clustering directly: the radius
l = log(8C + 1)/κ_μ works for every centre. This is why route (1) cannot be a route FROM the
susceptibility: its natural output already contains the gap. -/
theorem clustering_of_effectiveMassDomination {m₀ lam μ C K : ℝ} (hm : m₀ ≠ 0) (hlam : 0 ≤ lam)
    (hμ : μ ≠ 0) (hC : 0 ≤ C) (hD : EffectiveMassDomination m₀ lam μ C)
    (hK : UniformSusceptibility m₀ lam K) :
    ∃ m : ℝ, 0 < m ∧ FiniteCutoffClustering m₀ lam m := by
  have hκ := rg_kappa_pos hμ
  set l : ℝ := Real.log (8 * C + 1) / rg_kappa μ with hl
  have hl0 : 0 ≤ l := div_nonneg (Real.log_nonneg (by linarith)) hκ.le
  have hV : VarSmallBoundarySum m₀ lam l (1 / 2) := by
    intro n k x
    refine ⟨l, hl0, le_rfl, (sh2_bdrySum_le_of_domination hμ hC hD hl0 x).trans ?_⟩
    have h2 : rg_kappa μ * l = Real.log (8 * C + 1) := by rw [hl]; field_simp
    rw [h2]
    have h1 := rg_two_div_cosh_le (Real.log (8 * C + 1))
    rw [Real.exp_neg, Real.exp_log (by linarith)] at h1
    calc C * (2 / Real.cosh (Real.log (8 * C + 1))) ≤ C * (4 * (8 * C + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 hC
      _ = 4 * C / (8 * C + 1) := by ring
      _ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  exact clustering_of_varSmallBoundarySum hm hlam hl0 (by norm_num) (by norm_num) hV hK

end PP2Target

