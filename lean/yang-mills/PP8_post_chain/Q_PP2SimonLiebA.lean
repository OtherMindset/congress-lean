import LongTable.Q_PP2Green
import LongTable.P_mww55rjp_sgsnkh

/-!
Part A of PP2SimonLieb (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2SimonLieb.lean)
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M3, session 1.
The Simon–Lieb inequality for the quartic Dirichlet-box model of `P_mww4cze7_bk8bxu`
(namespace `PP2Target`): statement, proof route, first lemmas, and the M6 consumer.

Source: Brydges–Fröhlich–Spencer, CMP 83 (1982) 123–150 (uploaded copy, read through the site):
Theorem 5.1 (strong Gaussian domination ⟨S_i F⟩ ≤ Σ_j ⟨S_i S_j⟩⟨∂F/∂S_j⟩ for F with positive
coefficients, proved by the random-walk representation (5.5) and Griffiths II monotonicity in the
local times); Theorem 6.1 (Lieb–Rivasseau form of Simon's inequality, proved from 5.1 by
decoupling the bonds across ∂Ω, (6.2)); §7, (7.3)–(7.4) and "successive iterations".

NORMALISATION. ε = `spacing n`. `dirAction = ε² Σ_bonds ((Δφ)/ε)² + ε² m₀² Σ φ²
= Σ_bonds (Δφ)² + ε² m₀² Σ φ²`, so −½ dirAction = Σ_{u<v} J_uv φ_u φ_v − ½ Σ_x (4 + ε² m₀²) φ_x²
with J_uv = −ε² dirOp u v (= 1 for nearest neighbours, 0 otherwise; the explicit entries are
node M1's `dirOp_nn`/`dirOp_far`, not used here). We define `bondJ u v = −ε² · dirOp n k 0 u v`
(the mass enters only the diagonal), so the Simon–Lieb coupling is J_b = 1, independent of ε, as in
BFS (7.3) (where J = 1 and the sum runs over pairs z ∈ Ω, z' ∉ Ω, |z − z'| = δ). The diagonal
coefficient is 4 + ε² m₀² at EVERY site of the box (each box site has four bonds in `bondSet`,
those leaving the box included): Dirichlet, not free, boundary conditions.

DEFINITIONS (the statement).
* `twoPt n k m₀ λ x y`: the normalised two-point function ⟨φ_x φ_y⟩ of the quartic box measure
  (`dweight` with P = X⁴), on the convention of `ZD` (ratio of Bochner integrals).
* `regionTwoPt n k m₀ λ B x y`: the same for the measure on fields supported in a region
  B ⊆ box (Dirichlet on B: integrate over `{x // x ∈ B} → ℝ`, extend by zero, `zeroExt`).
* `SimonLiebIneq m₀ λ`: for every n, k, region B, x ∈ B, y ∉ B,
    twoPt x y ≤ Σ_{u ∈ B} Σ_{v ∈ Bᶜ} bondJ u v · regionTwoPt B x u · twoPt v y.
  `SimonLiebTarget`: SimonLiebIneq m₀ λ for every m₀ ≠ 0 and λ ≥ 0 (the target of M3).
* `M6Consumer`: SimonLiebIneq + Griffiths I for region measures + the small boundary sum
  Σ_{u ∈ B(x,l)} Σ_{v ∉ B(x,l)} J_uv ⟨φ_x φ_u⟩_{B(x,l)} ≤ γ < 1 (B(x,l) the physical sup-norm ball,
  node M5) + a uniform bound twoPt ≤ K at physical distance ≥ 1 ⟹ twoPt ≤ C₀ e^{−m d} at distance
  d ≥ 1, uniformly in n, k: exactly the hypothesis hG of `conditional_clustering`.
  The proved implication is conditional: SimonLiebIneq, SmallBoundarySum and UniformBaseBound are
  all UNPROVEN for the interacting model, and `clustering_of_simonLieb` additionally assumes
  Newman's inequality `hN`. A route review recommends replacing the pointwise `UniformBaseBound`
  by a smeared region-susceptibility bound (planned; not in this file).

PROOF ROUTE for `SimonLiebTarget` (sessions 2–5). BFS's, with the random-walk SERIES replaced by a
finite-dimensional maximum principle; no walks, no infinite sums.
(R1) Decoupling (this file, DONE): dweight φ = decWeight_B φ · exp(Σ_{u∈B,v∉B} J_uv φ_u φ_v) · const,
   decWeight_B φ = dweight(φ|_B) · dweight(φ|_{Bᶜ}); integrals against decWeight_B factor, and the
   decoupled two-point function of B-sites is `regionTwoPt B`. This is BFS (6.2).
(R2) Local-time family: for τ ∈ [0,∞)^ι the quartic single-site weight e^{−f(φ²/2)}, f(s) = αs + βs²
   (β = 4λε² ≥ 0), shifted to e^{−f(φ²/2 + τ_x)} = (const) · e^{−βτ_x φ_x²} · e^{−f(φ²/2)}: the same
   model with site masses increased. One-site integration by parts in the local time (1-D calculus +
   Fubini): [φ_i G]_τ = ∫_0^∞ ds ([∂_i G]_{τ+s e_i} + Σ_j J_ij [φ_j G]_{τ+s e_i}). This is the
   generator of BFS's random-walk representation (their Theorem 2.2, (5.5)).
(R3) Griffiths II in the cone 𝒞 = {g · exp Q : g, Q with nonnegative coefficients} for site-dependent
   even weights (duplicate variables; the (s, d) = (φ + φ', φ − φ') sign flips are the coordinate
   involutions (φ, φ') ↦ (φ', φ) and (φ, φ') ↦ (−φ', −φ), so the Griffiths I sign-averaging lemma
   applies with no change of variables). Consequence: ⟨H⟩_τ' ≤ ⟨H⟩_τ for τ' ≥ τ, H ∈ 𝒞
   (d/dt = −β⟨H; Σ δ_x φ_x²⟩ ≤ 0, or a t-integral). Node M2's Griffiths II, in this form.
(R4) Strong Gaussian domination (BFS Theorem 5.1) for G ∈ 𝒞: with c_j = ⟨∂_j G⟩_{τ⁰} and
   D_i(τ) = Σ_j c_j [φ_i φ_j]_τ − [φ_i G]_τ, (R2) gives D = (nonnegative source, by (R3)) + K D with
   (K D)_i(τ) = Σ_k J_ik ∫_0^∞ D_k(τ + s e_i) ds; in the weighted norm sup_τ |D(τ)| e^{β'|τ|₁},
   β' > max_i Σ_k J_ik = 4 (possible: f(u+τ) − f(u) ≥ ατ + βτ², and α = 4 + ε²m₀² > 4 when λ = 0),
   ‖K‖ ≤ 4/β' < 1, so D⁻ ≤ K D⁻ forces D⁻ = 0. Replaces summing the walk series of BFS (5.5)–(5.6).
(R5) Simon–Lieb (BFS Theorem 6.1): apply (R4) to the decoupled measure, i = x, G = φ_y · Φ,
   Φ = exp(Σ_{u∈B,v∉B} J φ_u φ_v) ∈ 𝒞 (no polynomial approximation of Φ is needed: 𝒞 contains it);
   ∂_u(φ_y Φ) = φ_y Σ_v J_uv φ_v Φ for u ∈ B; ⟨φ_x φ_u⟩_dec = regionTwoPt B x u by (R1), and 0 for
   u ∉ B; divide by ⟨Φ⟩_dec and use (R1) again. Integrability: λ > 0 or m₀ ≠ 0 (node M2's
   `integrable_dweight`).
Why this route: it needs only finite-dimensional integrals; it reuses Griffiths I's sign-averaging
(PP2Griffiths) and Gaussian-type growth bounds; the alternatives cost more: Simon's proof uses the
Lebowitz inequality (itself a case of (R4)) and gives only the unimproved form (⟨⟩_Λ instead of
⟨⟩_B in the first factor, useless for M5/M6, where the first factor must be a fixed-box quantity);
Lieb's and Rivasseau's proofs, as far as we know (their papers were not read), are for Ising
spins and reach φ⁴ only through the Griffiths–Simon approximation (a weak-limit theorem); GHS needs the Ellis–Monroe–Newman machinery; and the literal
random-walk representation needs walk combinatorics and a convergent series. `gauss_ibp_cov` does
not do (R2): with Wick ordering the Gaussian part has mass² ε²m₀² − 12λε² c, c = freeVar ~ log(1/ε),
so a Gaussian-reference IBP gives no ε-uniform monotone structure; the local-time IBP needs none.

FORMALIZED here (no sorry; axioms propext, Classical.choice, Quot.sound).
* `dirOp_offDiag_mass`, `bondJ_nonneg`, `bondJ_symm`, `bondJ_local` (J_uv ≠ 0 ⟹ lattice
  coordinates differ by ≤ 1), `supDist_bondJ` (J_uv ≠ 0 ⟹ physical sup-distance ≤ ε).
* `cross_term`, `dirAction_split`: dirAction φ = dirAction φ|_B + dirAction φ|_{Bᶜ}
  − 2 Σ_{u∈B,v∈Bᶜ} J_uv φ_u φ_v.
* `dweight_split`: dweight φ = decWeight_B φ · exp(Σ J φ_u φ_v) · exp(λε² |Λ| :P:(0)) (any P).
* `integral_decoupled`: ∫ G(φ|_B) · decWeight_B φ = (∫_{ℝ^B} G(zeroExt ψ) dweight(zeroExt ψ)) ·
  (∫_{ℝ^{Bᶜ}} dweight(zeroExtC η)), with no integrability hypothesis (zero-coupling factorisation).
* `decoupled_twoPt`: the decoupled two-point function of the B-fields is `regionTwoPt B`
  (given that the complement partition function is ≠ 0).
* `twoPt_eq_decoupled`: twoPt x y = ⟨φ_x φ_y Φ⟩_dec / ⟨Φ⟩_dec (BFS (6.2)).
* `iterate_bound`, `geom_le_exp` (abstract Simon iteration), `m6Consumer : M6Consumer`, and
  `clustering_of_simonLieb`: with Newman's inequality (H1 of `conditional_clustering`, with
  G = twoPt) and |ZD| ≤ 1, the four inputs above give `FiniteCutoffClustering m₀ λ m` for some m > 0.

NOT formalized: (R2)–(R5); Griffiths I for region measures (`RegionGriffithsI`, node M2's argument
applies verbatim on ℝ^B); twoPt = regionTwoPt univ; positivity of partition functions.
A FINDING for M6/M5: BFS §7 says "successive iterations of (7.3) and (7.4) imply exponential
decay". The iteration ends on a two-point function at short distance, whose only a-priori bound is
⟨φ²⟩ ~ (2π)⁻¹ log(1/ε) (Wick ordering does not remove it from ⟨φ_x φ_x⟩). So an ε-uniform decay
bound needs, besides (7.4), a uniform bound K on twoPt at physical distance ≥ 1 (`UniformBaseBound`);
we did not find one stated in the passages of BFS we read. `m6Consumer` makes it an explicit hypothesis. It is not a consequence of
(7.4) at all scales: at scales r ≪ 1 the boundary sum is ≈ 1, not < 1 (heuristically; for the
free field it is the exit probability of a walk killed at rate ≈ ε²m₀²/4 per step).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
open MeasureTheory Matrix Finset

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## The statement -/

/-- The quartic Dirichlet weight (`dweight` with P = X⁴). -/
abbrev qweight (n k : ℕ) (m₀ lam : ℝ) : DField n k → ℝ :=
  dweight n k m₀ lam (Polynomial.X ^ 4)

/-- The normalised two-point function ⟨φ_x φ_y⟩ of the quartic Dirichlet-box measure. -/
def twoPt (n k : ℕ) (m₀ lam : ℝ) (x y : DSite n k) : ℝ :=
  (∫ φ : DField n k, φ x * φ y * qweight n k m₀ lam φ) / ∫ φ : DField n k, qweight n k m₀ lam φ

/-- Extension by zero of a field on a region B. -/
def zeroExt (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) : DField n k :=
  fun x => if h : x ∈ B then ψ ⟨x, h⟩ else 0

/-- Extension by zero of a field on the complement of B. -/
def zeroExtC (B : Finset (DSite n k)) (η : {x // x ∉ B} → ℝ) : DField n k :=
  fun x => if h : x ∈ B then 0 else η ⟨x, h⟩

/-- The two-point function of the region B with Dirichlet (zero) boundary values on its
complement: the measure on fields supported in B, with the same action and Wick polynomial. -/
def regionTwoPt (n k : ℕ) (m₀ lam : ℝ) (B : Finset (DSite n k)) (x y : DSite n k) : ℝ :=
  (∫ ψ : {z // z ∈ B} → ℝ, zeroExt B ψ x * zeroExt B ψ y * qweight n k m₀ lam (zeroExt B ψ)) /
    ∫ ψ : {z // z ∈ B} → ℝ, qweight n k m₀ lam (zeroExt B ψ)

/-- The coupling of the bond {u, v} in −½ dirAction: J_uv = −ε² dirOp u v (u ≠ v); it is 1 for
nearest neighbours and 0 otherwise. -/
def bondJ (n k : ℕ) (u v : DSite n k) : ℝ := -(spacing n ^ 2 * dirOp n k 0 u v)

/-- **The Simon–Lieb inequality** (Lieb–Rivasseau form, BFS CMP 83 Theorem 6.1 with F = φ_y)
for the quartic Dirichlet-box model at (m₀, λ). -/
def SimonLiebIneq (m₀ lam : ℝ) : Prop :=
  ∀ (n k : ℕ) (B : Finset (DSite n k)) (x y : DSite n k), x ∈ B → y ∉ B →
    twoPt n k m₀ lam x y ≤
      ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * regionTwoPt n k m₀ lam B x u * twoPt n k m₀ lam v y

/-- The target of node M3. -/
def SimonLiebTarget : Prop :=
  ∀ m₀ lam : ℝ, m₀ ≠ 0 → 0 ≤ lam → SimonLiebIneq m₀ lam

/-! ## The coupling J -/

theorem dirOp_offDiag_mass (m₀ : ℝ) {u v : DSite n k} (huv : u ≠ v) :
    dirOp n k m₀ u v = dirOp n k 0 u v := by
  simp only [dirOp, Matrix.add_apply, Matrix.smul_apply, one_apply_ne huv, smul_eq_mul,
    mul_zero, add_zero]

theorem bondJ_nonneg {u v : DSite n k} (huv : u ≠ v) : 0 ≤ bondJ n k u v :=
  neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (dirOp_offDiag_nonpos 0 huv))

theorem bondJ_symm (u v : DSite n k) : bondJ n k u v = bondJ n k v u := by
  rw [bondJ, bondJ, dirOp_symm]

theorem extVec_ne_zero {q : ℤ × ℤ} {w : DSite n k} (h : (extVec q : DField n k) w ≠ 0) :
    q.1 = ((w.1 : ℕ) : ℤ) ∧ q.2 = ((w.2 : ℕ) : ℤ) := by
  unfold extVec ext at h
  split_ifs at h with hq
  · rw [Pi.single_apply] at h
    split_ifs at h with hpt
    · subst hpt
      simp only
      omega
    · exact absurd rfl h
  · exact absurd rfl h

theorem bondVec_ne_zero {p q : ℤ × ℤ} {w : DSite n k} (h : (bondVec p q : DField n k) w ≠ 0) :
    (q.1 = ((w.1 : ℕ) : ℤ) ∧ q.2 = ((w.2 : ℕ) : ℤ)) ∨
      (p.1 = ((w.1 : ℕ) : ℤ) ∧ p.2 = ((w.2 : ℕ) : ℤ)) := by
  unfold bondVec at h
  rw [Pi.sub_apply] at h
  by_cases hq : (extVec q : DField n k) w = 0
  · right
    have hp : (extVec p : DField n k) w ≠ 0 := by
      intro hp; rw [hq, hp] at h; exact h (sub_zero 0)
    exact extVec_ne_zero hp
  · left; exact extVec_ne_zero hq

theorem abs_natCast_sub_le_one {a b : ℕ} (h1 : (a : ℤ) ≤ b + 1) (h2 : (b : ℤ) ≤ a + 1) :
    |(a : ℝ) - (b : ℝ)| ≤ 1 := by
  rw [abs_le]
  constructor
  · have : ((b : ℤ) : ℝ) ≤ ((a : ℤ) : ℝ) + 1 := by exact_mod_cast h2
    push_cast at this; linarith
  · have : ((a : ℤ) : ℝ) ≤ ((b : ℤ) : ℝ) + 1 := by exact_mod_cast h1
    push_cast at this; linarith

/-- **Locality of the coupling:** J_uv ≠ 0 only between sites whose lattice coordinates differ
by at most one. -/
theorem bondJ_local {u v : DSite n k} (h : bondJ n k u v ≠ 0) :
    |((u.1 : ℕ) : ℝ) - ((v.1 : ℕ) : ℝ)| ≤ 1 ∧ |((u.2 : ℕ) : ℝ) - ((v.2 : ℕ) : ℝ)| ≤ 1 := by
  have hD : dirOp n k 0 u v ≠ 0 := by
    intro h0; apply h; rw [bondJ, h0, mul_zero, neg_zero]
  have hS : ∑ p ∈ bondSet n k, ((bondH p : DField n k) u * bondH p v
      + (bondV p : DField n k) u * bondV p v) ≠ 0 := by
    intro h0; apply hD
    simp only [dirOp, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
      smul_eq_mul]
    rw [h0]; simp
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  by_cases hH : (bondH p : DField n k) u * bondH p v = 0
  · rw [hH, zero_add] at hp
    have hu := bondVec_ne_zero (left_ne_zero_of_mul hp)
    have hv := bondVec_ne_zero (right_ne_zero_of_mul hp)
    simp only at hu hv
    constructor
    · apply abs_natCast_sub_le_one <;> omega
    · apply abs_natCast_sub_le_one <;> omega
  · have hu := bondVec_ne_zero (left_ne_zero_of_mul hH)
    have hv := bondVec_ne_zero (right_ne_zero_of_mul hH)
    simp only at hu hv
    constructor
    · apply abs_natCast_sub_le_one <;> omega
    · apply abs_natCast_sub_le_one <;> omega

/-! ## The sup-norm distance -/

theorem supDist_self (p : Plane) : supDist p p = 0 := by simp [supDist]

theorem supDist_comm (p q : Plane) : supDist p q = supDist q p := by
  simp only [supDist, abs_sub_comm (p 0), abs_sub_comm (p 1)]

theorem supDist_triangle (p q r : Plane) : supDist p r ≤ supDist p q + supDist q r := by
  unfold supDist
  have h0 := abs_sub_le (p 0) (q 0) (r 0)
  have h1 := abs_sub_le (p 1) (q 1) (r 1)
  refine max_le ?_ ?_
  · linarith [le_max_left |p 0 - q 0| |p 1 - q 1|, le_max_left |q 0 - r 0| |q 1 - r 1|]
  · linarith [le_max_right |p 0 - q 0| |p 1 - q 1|, le_max_right |q 0 - r 0| |q 1 - r 1|]

theorem supDist_bondJ {u v : DSite n k} (h : bondJ n k u v ≠ 0) :
    supDist (dpos n k u) (dpos n k v) ≤ spacing n := by
  obtain ⟨h1, h2⟩ := bondJ_local h
  have hε := spacing_pos n
  unfold supDist
  rw [dpos_zero, dpos_zero, dpos_one, dpos_one]
  have e1 : spacing n * ((u.1 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((v.1 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((u.1 : ℕ) : ℝ) - ((v.1 : ℕ) : ℝ)) := by ring
  have e2 : spacing n * ((u.2 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((v.2 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((u.2 : ℕ) : ℝ) - ((v.2 : ℕ) : ℝ)) := by ring
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hε]
  refine max_le ?_ ?_
  · calc spacing n * _ ≤ spacing n * 1 := mul_le_mul_of_nonneg_left h1 hε.le
      _ = spacing n := mul_one _
  · calc spacing n * _ ≤ spacing n * 1 := mul_le_mul_of_nonneg_left h2 hε.le
      _ = spacing n := mul_one _

/-! ## Decomposition of the action across a region (BFS (6.2)) -/

/-- The field restricted to B (zero outside). -/
def restrictIn (B : Finset (DSite n k)) (φ : DField n k) : DField n k :=
  fun x => if x ∈ B then φ x else 0

/-- The field restricted to the complement of B (zero on B). -/
def restrictOut (B : Finset (DSite n k)) (φ : DField n k) : DField n k :=
  fun x => if x ∈ B then 0 else φ x

theorem restrict_add (B : Finset (DSite n k)) (φ : DField n k) :
    restrictIn B φ + restrictOut B φ = φ := by
  funext x
  simp only [Pi.add_apply, restrictIn, restrictOut]
  split_ifs <;> simp

/-- The boundary coupling Σ_{u ∈ B, v ∉ B} J_uv φ_u φ_v. -/
def bdryCoupling (B : Finset (DSite n k)) (φ : DField n k) : ℝ :=
  ∑ u ∈ B, ∑ v ∈ Bᶜ, bondJ n k u v * φ u * φ v

theorem cross_term (B : Finset (DSite n k)) (M : Matrix (DSite n k) (DSite n k) ℝ)
    (φ : DField n k) :
    restrictIn B φ ⬝ᵥ M *ᵥ restrictOut B φ = ∑ u ∈ B, ∑ v ∈ Bᶜ, M u v * φ u * φ v := by
  have h1 : ∀ u, restrictIn B φ u * (M *ᵥ restrictOut B φ) u =
      if u ∈ B then ∑ v ∈ Bᶜ, M u v * φ u * φ v else 0 := by
    intro u
    simp only [mulVec, dotProduct, restrictIn]
    split_ifs with hu
    · rw [← Fintype.sum_ite_mem Bᶜ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ B
      · simp [restrictOut, hv]
      · simp [restrictOut, hv]; ring
    · simp
  simp only [dotProduct]
  rw [Finset.sum_congr rfl fun u _ => h1 u, Fintype.sum_ite_mem]

/-- **The action across ∂B:** dirAction φ = dirAction φ|_B + dirAction φ|_{Bᶜ}
− 2 Σ_{u ∈ B, v ∉ B} J_uv φ_u φ_v. -/
theorem dirAction_split (m₀ : ℝ) (B : Finset (DSite n k)) (φ : DField n k) :
    dirAction n k m₀ φ = dirAction n k m₀ (restrictIn B φ) + dirAction n k m₀ (restrictOut B φ)
      - 2 * bdryCoupling B φ := by
  have hsym : restrictOut B φ ⬝ᵥ dirOp n k m₀ *ᵥ restrictIn B φ
      = restrictIn B φ ⬝ᵥ dirOp n k m₀ *ᵥ restrictOut B φ := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dirOp_transpose, dotProduct_comm]
  have hcross : spacing n ^ 2 * (restrictIn B φ ⬝ᵥ dirOp n k m₀ *ᵥ restrictOut B φ)
      = -bdryCoupling B φ := by
    rw [cross_term, bdryCoupling, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    have huv : u ≠ v := by
      rintro rfl; exact (Finset.mem_compl.mp hv) hu
    rw [bondJ, dirOp_offDiag_mass m₀ huv]
    ring
  conv_lhs => rw [← restrict_add B φ]
  simp only [dirAction_eq_quad]
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym]
  linear_combination 2 * hcross

/-- The decoupled weight: the box weight with the couplings across ∂B removed (up to a
constant), i.e. the product of the B-weight and the Bᶜ-weight. -/
def decWeight (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (B : Finset (DSite n k))
    (φ : DField n k) : ℝ :=
  dweight n k m₀ lam P (restrictIn B φ) * dweight n k m₀ lam P (restrictOut B φ)

/-- **Factorisation of the weight across ∂B** (BFS (6.2)):
dweight φ = decWeight_B φ · exp(Σ_{u∈B, v∉B} J_uv φ_u φ_v) · exp(λ ε² |Λ| :P:(0)). -/
theorem dweight_split (m₀ lam : ℝ) (P : Polynomial ℝ) (B : Finset (DSite n k))
    (φ : DField n k) :
    dweight n k m₀ lam P φ = decWeight n k m₀ lam P B φ * Real.exp (bdryCoupling B φ)
      * Real.exp (lam * spacing n ^ 2 *
          ((Fintype.card (DSite n k) : ℝ) * wickPoly P (freeVar n m₀) 0)) := by
  have hW : ∑ x : DSite n k, wickPoly P (freeVar n m₀) (φ x) =
      ∑ x : DSite n k, wickPoly P (freeVar n m₀) (restrictIn B φ x)
        + ∑ x : DSite n k, wickPoly P (freeVar n m₀) (restrictOut B φ x)
        - (Fintype.card (DSite n k) : ℝ) * wickPoly P (freeVar n m₀) 0 := by
    have hc : (Fintype.card (DSite n k) : ℝ) * wickPoly P (freeVar n m₀) 0
        = ∑ _x : DSite n k, wickPoly P (freeVar n m₀) 0 := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [restrictIn, restrictOut]
    split_ifs <;> ring
  unfold decWeight dweight
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [dirAction_split m₀ B φ, hW]
  ring

/-! ## The zero-coupling factorisation -/

theorem restrictIn_symm (B : Finset (DSite n k)) (z : ({x // x ∈ B} → ℝ) × ({x // x ∉ B} → ℝ)) :
    restrictIn B ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : DSite n k => ℝ)
      (fun x => x ∈ B)).symm z) = zeroExt B z.1 := by
  funext x
  by_cases hx : x ∈ B <;>
    simp [restrictIn, zeroExt, hx, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]

theorem restrictOut_symm (B : Finset (DSite n k)) (z : ({x // x ∈ B} → ℝ) × ({x // x ∉ B} → ℝ)) :
    restrictOut B ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : DSite n k => ℝ)
      (fun x => x ∈ B)).symm z) = zeroExtC B z.2 := by
  funext x
  by_cases hx : x ∈ B <;>
    simp [restrictOut, zeroExtC, hx, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]

end PP2Target

end
