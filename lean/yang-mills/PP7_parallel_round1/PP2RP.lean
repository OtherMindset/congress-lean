import LongTable.PP2Griffiths2

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Hamiltonian track H, session 1.
Reflection positivity (RP) of the lattice Dirichlet-box measure `PP2Target.dweight` of
#mww4cze7-bk8bxu, for the BOND reflection of the first lattice coordinate, i ↦ N − 1 − i
(N = 2^(n+k) = `boxN n k`, n + k ≥ 1 so N is even; the plane lies between columns N/2 − 1 and
N/2, i.e. between sites). In physical coordinates (`dpos`: x₀ = εi − L/2) the plane is at
x₀ = −ε/2, so the lattice time zero is offset by half a spacing from the continuum t = 0 of
`PP2TargetV4.reflect`; this is the usual lattice convention and disappears as ε → 0.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* `rp_kernel` (abstract, any finite α, β, c : β → α): if g · exp(Σ_j ψ(c j)²/2) is integrable,
    0 ≤ ∫∫ g(ψ) g(η) exp(Σ_j ψ(c j) η(c j)) dψ dη.
  Proof: power series of exp, exchanged with the integral by dominated convergence
  (`hasSum_integral_of_dominated_convergence`, majorant |g g| e^{|s|} ≤ |g e^{·}| ⊗ |g e^{·}| via
  |ab| ≤ (a² + b²)/2); the m-th term is (1/m!) Σ_{w : Fin m → β} (∫ g · ∏_i ψ(c(w i)))² by
  `Fintype.sum_pow` and `integral_prod_mul` (integrability of g · monomial from
  S^m ≤ m! e^S, S = Σ_j |ψ(c j)| ≤ (|β| + Σ_j ψ(c j)²)/2). No finite-dimensional shortcut was used.
* Half-box coordinates: `HSite n k` = Fin (N/2) × Fin N; `splitEquiv` : HSite ⊕ HSite ≃ DSite,
  inl (a, j) ↦ (N/2 + a, j), inr (a, j) ↦ (N/2 − 1 − a, j); `glue (ψ, η)` the field with right
  half ψ and reflected left half η; `glueME` the same as a measurable equivalence, measure
  preserving (`glueME_mp`), `integral_glue` (change of variables). `reflX` (i, j) ↦ (N−1−i, j);
  `glue_reflX`: reflecting glue (ψ, η) gives glue (η, ψ).
* `Jnn_closed`: closed form of PP2Griffiths2's coupling, Jnn x y = [x = y + e₁] + [x = y + e₂]
  (listed as NOT formalized there). `Jnn_inl_inl`, `Jnn_inr_inr`, `Jnn_inl_inr`, `Jnn_inr_inl`:
  its four blocks across the plane; the only crossing bonds are horizontal between columns N/2 and
  N/2 − 1, coupling +1 (sign: dweight = exp(+Σ Jnn φφ) · ∏ w, Jnn ≥ 0).
* (a) `dweight_glue`: dweight(glue(ψ, η)) = B(ψ) · B(η) · exp(Σ_j ψ(0, j) η(0, j)), with
  B = `Bh` = exp(halfQ) · ∏ sw (the half-box weight; any P, any m₀, λ). `dweight_reflX`: dweight
  is reflection invariant. (Done directly from `dweight_eq_ferro`; `dirAction_split` of
  PP2SimonLieb was not needed.)
* (b) `rp_dweight`: for F with `RightLocal F` (F φ depends only on φ on {i ≥ N/2}) and
  G(ψ) = F(glue(ψ, 0)), if G · B · exp(Σ_j ψ(0, j)²/2) is integrable, then
    0 ≤ ∫ F(φ ∘ reflX) · F(φ) · dweight(φ) dφ          (any P, m₀, λ).
  `rp_dweight_bounded`: the hypothesis holds for every bounded measurable right-local F in the
  quartic model with m₀ ≠ 0, λ ≥ 0 (key identity `Bh_bexp_sq`: (B · e^{|ψ₀|²/2})² =
  dweight(glue(ψ, ψ)), then `dweight_le`'s Gaussian majorant). Bochner caveat:
  `integrable_rp_integrand` proves the integrand integrable in that case, so the inequality is
  about a genuine integral, not the junk value 0.

NOT formalized.
* RP for polynomial (unbounded) F: `rp_dweight` covers it once G · B · e^{|ψ₀|²/2} is shown
  integrable (polynomial × the Gaussian majorant, as in PP2Griffiths3); not done here. Complex
  F (e.g. e^{iφ(f)}, needed for the OS form ⟪ψ f, ψ g⟫ of `OSGap`): ∫ conj(ΘF) F dweight ≥ 0
  follows from the real case applied to Re F and Im F plus the symmetry
  ∫ ΘA · B = ∫ ΘB · A (from `dweight_reflX`); not written.
* Site reflection (plane through a column), other reflection directions, time-translation
  structure.

WHAT THE HAMILTONIAN TRACK NEEDS NEXT (towards `HamiltonianGap` / `OSGap` of PP2TargetV4).
1. Transfer matrix at finite lattice: write dweight as a product over columns,
   ∏_i K(φ_i, φ_{i+1}) · ∏_i V(φ_i) with Dirichlet ends; T = V^{1/2} K V^{1/2} is a positive
   (by RP / Gaussian kernel positivity) self-adjoint Hilbert–Schmidt operator on L²(ℝ^N);
   T^t, t ∈ εℕ, is the discrete-time semigroup. Correlations of column observables are
   ⟨Ω_D, A T^{t} B Ω_D⟩ with boundary vectors Ω_D from the Dirichlet ends (not the vacuum).
2. Finite OS reconstruction: the RP form ⟨F, G⟩ = ∫ ΘF · G · dweight on right-local F, quotient
   by null vectors, completion; time shift by one column is a contraction on it (needs RP of the
   shifted box, or the transfer matrix of 1).
3. `PP2SemigroupGap.semigroup_gap` (namespace PP2Gap; the module `LongTable.P_mwvi83yc_ictv1e`
   named in the brief does NOT exist in this tree, the file present is LongTable/PP2SemigroupGap.lean)
   takes T : ℝ → (E →L E), self-adjoint, semigroup for s, t ≥ 0, invariant unit Ω, and decay
   re⟪v, T s v⟫ ≤ C e^{−ms} on a dense set ⟂ Ω. Feeding it requires: continuous time (lattice
   time is discrete — either restrict to t ∈ εℕ with a discrete-time variant of the lemma, or
   wait for the limit ε → 0), the vacuum (infinite-volume limit; in the box the Dirichlet ends
   break time-translation invariance), and the decay estimate, which is exactly the clustering
   of PP2TargetV3/V4 (`FiniteCutoffClustering`) transported to the OS form. So RP + clustering
   + a limit construction are the three inputs; this file supplies the first, at finite cutoff.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Finset Real

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2RP

/-! ## Abstract reflection positivity for the kernel exp(Σ_j a_j b_j) -/

section Abstract

variable {α β : Type*} [Fintype α] [Fintype β] (c : β → α)

/-- The boundary coupling Σ_j ψ(c j) η(c j). -/
def bcoup (ψ η : α → ℝ) : ℝ := ∑ j, ψ (c j) * η (c j)

/-- The Gaussian-type majorant exp(Σ_j ψ(c j)² / 2). -/
def bexp (ψ : α → ℝ) : ℝ := Real.exp (∑ j, ψ (c j) ^ 2 / 2)

/-- The monomial ∏_i ψ(c (w i)). -/
def bmono {m : ℕ} (w : Fin m → β) (ψ : α → ℝ) : ℝ := ∏ i, ψ (c (w i))

theorem bexp_pos (ψ : α → ℝ) : 0 < bexp c ψ := Real.exp_pos _

theorem abs_bcoup_le (ψ η : α → ℝ) :
    |bcoup c ψ η| ≤ ∑ j, ψ (c j) ^ 2 / 2 + ∑ j, η (c j) ^ 2 / 2 := by
  unfold bcoup
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  nlinarith [sq_nonneg (|ψ (c j)| - |η (c j)|), sq_abs (ψ (c j)), sq_abs (η (c j))]

theorem abs_bmono_le {m : ℕ} (w : Fin m → β) (ψ : α → ℝ) :
    |bmono c w ψ| ≤ (m.factorial : ℝ) * Real.exp ((Fintype.card β : ℝ) / 2) * bexp c ψ := by
  set S := ∑ j, |ψ (c j)| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : |bmono c w ψ| ≤ S ^ m := by
    unfold bmono
    rw [Finset.abs_prod]
    calc ∏ i, |ψ (c (w i))| ≤ ∏ _i : Fin m, S :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
            Finset.single_le_sum (f := fun j => |ψ (c j)|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ (w i))
      _ = S ^ m := by simp
  have h2 : S ^ m ≤ (m.factorial : ℝ) * Real.exp S := by
    have := Real.pow_div_factorial_le_exp (x := S) hS0 m
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hf] at this
    linarith
  have h3 : S ≤ (Fintype.card β : ℝ) / 2 + ∑ j, ψ (c j) ^ 2 / 2 := by
    have : S ≤ ∑ j : β, (1 / 2 + ψ (c j) ^ 2 / 2) :=
      Finset.sum_le_sum fun j _ => by
        nlinarith [sq_nonneg (|ψ (c j)| - 1), sq_abs (ψ (c j))]
    rw [Finset.sum_add_distrib] at this
    simpa [Finset.card_univ, div_eq_mul_inv] using this
  have hf : (0 : ℝ) ≤ m.factorial := by positivity
  calc |bmono c w ψ| ≤ (m.factorial : ℝ) * Real.exp S := h1.trans h2
    _ ≤ (m.factorial : ℝ) * Real.exp ((Fintype.card β : ℝ) / 2 + ∑ j, ψ (c j) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) hf
    _ = _ := by rw [Real.exp_add, bexp]; ring

theorem bcoup_pow (m : ℕ) (ψ η : α → ℝ) :
    bcoup c ψ η ^ m = ∑ w : Fin m → β, bmono c w ψ * bmono c w η := by
  unfold bcoup bmono
  rw [Fintype.sum_pow]
  exact Finset.sum_congr rfl fun w _ => Finset.prod_mul_distrib

theorem continuous_bexp : Continuous (bexp (α := α) c) := by
  unfold bexp; fun_prop

theorem continuous_bcoup : Continuous fun z : (α → ℝ) × (α → ℝ) => bcoup c z.1 z.2 := by
  unfold bcoup; fun_prop

theorem continuous_bmono {m : ℕ} (w : Fin m → β) : Continuous (bmono (α := α) c w) := by
  unfold bmono; fun_prop

/-- **Reflection positivity of the kernel exp(Σ_j a_j b_j)**: for any g with
g · exp(Σ_j ψ(c j)²/2) integrable,
∫∫ g(ψ) g(η) exp(Σ_j ψ(c j) η(c j)) dψ dη ≥ 0.
Proof: expand the exponential (dominated convergence); the m-th term is
(1/m!) Σ_w (∫ g · ∏_i ψ(c (w i)))². -/
theorem rp_kernel (g : (α → ℝ) → ℝ) (hg : Integrable fun ψ => g ψ * bexp c ψ) :
    0 ≤ ∫ z : (α → ℝ) × (α → ℝ), g z.1 * g z.2 * Real.exp (bcoup c z.1 z.2) := by
  have hE : ∀ ψ, 0 < bexp c ψ := fun ψ => Real.exp_pos _
  have hgm : AEStronglyMeasurable g := by
    have := hg.aestronglyMeasurable.mul
      ((continuous_bexp c).inv₀ fun ψ => (hE ψ).ne').aestronglyMeasurable
    refine this.congr (Filter.Eventually.of_forall fun ψ => ?_)
    simp [mul_assoc, mul_inv_cancel₀ (hE ψ).ne']
  rw [Measure.volume_eq_prod]
  -- integrability of g · bmono
  have hgM : ∀ {m : ℕ} (w : Fin m → β), Integrable fun ψ => g ψ * bmono c w ψ := by
    intro m w
    refine Integrable.mono' ((hg.norm).const_mul
      ((m.factorial : ℝ) * Real.exp ((Fintype.card β : ℝ) / 2)))
      (hgm.mul (continuous_bmono c w).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ψ => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hE ψ)]
    have := abs_bmono_le c w ψ
    have h0 := abs_nonneg (g ψ)
    calc |g ψ| * |bmono c w ψ|
        ≤ |g ψ| * ((m.factorial : ℝ) * Real.exp ((Fintype.card β : ℝ) / 2) * bexp c ψ) :=
          mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  -- each term of the series is nonnegative
  have hterm : ∀ m : ℕ, 0 ≤ ∫ z : (α → ℝ) × (α → ℝ),
      g z.1 * g z.2 * (bcoup c z.1 z.2 ^ m / m.factorial) ∂(volume.prod volume) := by
    intro m
    have heq : ∀ z : (α → ℝ) × (α → ℝ), g z.1 * g z.2 * (bcoup c z.1 z.2 ^ m / m.factorial)
        = (m.factorial : ℝ)⁻¹ * ∑ w : Fin m → β,
            (g z.1 * bmono c w z.1) * (g z.2 * bmono c w z.2) := by
      intro z
      rw [bcoup_pow, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    simp_rw [heq]
    rw [integral_const_mul, integral_finsetSum _ fun w _ => (hgM w).mul_prod (hgM w)]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => ?_)
    rw [integral_prod_mul (fun ψ => g ψ * bmono c w ψ) (fun ψ => g ψ * bmono c w ψ)]
    exact mul_self_nonneg _
  -- dominated convergence
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume.prod volume)
    (F := fun (m : ℕ) (z : (α → ℝ) × (α → ℝ)) =>
      g z.1 * g z.2 * (bcoup c z.1 z.2 ^ m / m.factorial))
    (f := fun z => g z.1 * g z.2 * Real.exp (bcoup c z.1 z.2))
    (fun m z => |g z.1 * g z.2| * (|bcoup c z.1 z.2| ^ m / m.factorial))
    (fun m => ((hgm.comp_fst).mul hgm.comp_snd).mul
      ((continuous_bcoup c).pow m |>.div_const _).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast])
    (Filter.Eventually.of_forall fun z =>
      ((NormedSpace.expSeries_div_summable (|bcoup c z.1 z.2| : ℝ)).mul_left _))
    ?_
    (Filter.Eventually.of_forall fun z => by
      have := (NormedSpace.expSeries_div_hasSum_exp (bcoup c z.1 z.2 : ℝ)).mul_left
        (g z.1 * g z.2)
      rwa [← Real.exp_eq_exp_ℝ] at this)
  · exact hasSum_le (fun m => hterm m) hasSum_zero hsum
  · -- the dominating function
    have htsum : ∀ z : (α → ℝ) × (α → ℝ),
        ∑' m : ℕ, |g z.1 * g z.2| * (|bcoup c z.1 z.2| ^ m / m.factorial)
          = |g z.1 * g z.2| * Real.exp |bcoup c z.1 z.2| := by
      intro z
      have := (NormedSpace.expSeries_div_hasSum_exp (|bcoup c z.1 z.2| : ℝ)).mul_left
        |g z.1 * g z.2|
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this.tsum_eq
    simp_rw [htsum]
    refine Integrable.mono' ((hg.norm).mul_prod hg.norm)
      (((hgm.comp_fst).mul hgm.comp_snd).norm.mul
        (continuous_bcoup c).abs.rexp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_pos (hE _), abs_of_pos (hE _)]
    have hb : Real.exp |bcoup c z.1 z.2| ≤ bexp c z.1 * bexp c z.2 := by
      rw [bexp, bexp, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (abs_bcoup_le c _ _)
    have := mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg (g z.1)) (abs_nonneg (g z.2)))
    linarith

end Abstract

/-! ## The Dirichlet box split across the reflection plane -/

section Lattice

open PP2Target PP2Griffiths

variable {n k : ℕ}

/-- Half the number of columns: the plane lies between columns N/2 − 1 and N/2. -/
def halfN (n k : ℕ) : ℕ := boxN n k / 2

theorem boxN_eq (hnk : 0 < n + k) : boxN n k = 2 * halfN n k := by
  unfold halfN boxN
  obtain ⟨m, hm⟩ : ∃ m, n + k = m + 1 := ⟨n + k - 1, by omega⟩
  rw [hm, pow_succ]
  omega

theorem halfN_pos (hnk : 0 < n + k) : 0 < halfN n k := by
  have h := boxN_eq hnk
  have : 0 < boxN n k := by unfold boxN; positivity
  omega

/-- Sites of a half box: (distance a from the plane, column index j), a < N/2. -/
abbrev HSite (n k : ℕ) := Fin (halfN n k) × Fin (boxN n k)

/-- inl (a, j) ↦ (N/2 + a, j) (right half), inr (a, j) ↦ (N/2 − 1 − a, j) (left half). -/
def splitFun (hnk : 0 < n + k) : HSite n k ⊕ HSite n k → DSite n k
  | .inl p => (⟨halfN n k + p.1, by have := boxN_eq hnk; have := p.1.isLt; omega⟩, p.2)
  | .inr p => (⟨halfN n k - 1 - p.1, by have := boxN_eq hnk; have := p.1.isLt; omega⟩, p.2)

theorem splitFun_bijective (hnk : 0 < n + k) : Function.Bijective (splitFun hnk) := by
  constructor
  · rintro (p | p) (q | q) h
    all_goals
      simp only [splitFun, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have := p.1.isLt
      have := q.1.isLt
    · exact congrArg Sum.inl (Prod.ext (Fin.ext (by omega)) h2)
    · have := halfN_pos hnk; omega
    · have := halfN_pos hnk; omega
    · exact congrArg Sum.inr (Prod.ext (Fin.ext (by omega)) h2)
  · intro x
    have := x.1.isLt
    have hN := boxN_eq hnk
    by_cases hx : halfN n k ≤ (x.1 : ℕ)
    · refine ⟨.inl (⟨x.1 - halfN n k, by omega⟩, x.2), ?_⟩
      exact Prod.ext (Fin.ext (by simp only [splitFun]; omega)) rfl
    · refine ⟨.inr (⟨halfN n k - 1 - x.1, by omega⟩, x.2), ?_⟩
      exact Prod.ext (Fin.ext (by simp only [splitFun]; omega)) rfl

/-- The box as two half boxes. -/
def splitEquiv (hnk : 0 < n + k) : HSite n k ⊕ HSite n k ≃ DSite n k :=
  Equiv.ofBijective _ (splitFun_bijective hnk)

theorem splitEquiv_inl (hnk : 0 < n + k) (p : HSite n k) :
    splitEquiv hnk (.inl p) =
      (⟨halfN n k + p.1, by have := boxN_eq hnk; have := p.1.isLt; omega⟩, p.2) := rfl

theorem splitEquiv_inr (hnk : 0 < n + k) (p : HSite n k) :
    splitEquiv hnk (.inr p) =
      (⟨halfN n k - 1 - p.1, by have := boxN_eq hnk; have := p.1.isLt; omega⟩, p.2) := rfl

/-- The field with right half ψ and reflected left half η:
φ(N/2 + a, j) = ψ(a, j), φ(N/2 − 1 − a, j) = η(a, j). -/
def glue (hnk : 0 < n + k) (z : (HSite n k → ℝ) × (HSite n k → ℝ)) : DField n k :=
  fun x => Sum.elim z.1 z.2 ((splitEquiv hnk).symm x)

@[simp] theorem glue_inl (hnk : 0 < n + k) (z : (HSite n k → ℝ) × (HSite n k → ℝ))
    (p : HSite n k) : glue hnk z (splitEquiv hnk (.inl p)) = z.1 p := by
  simp [glue]

@[simp] theorem glue_inr (hnk : 0 < n + k) (z : (HSite n k → ℝ) × (HSite n k → ℝ))
    (p : HSite n k) : glue hnk z (splitEquiv hnk (.inr p)) = z.2 p := by
  simp [glue]

theorem continuous_glue (hnk : 0 < n + k) : Continuous (glue hnk) := by
  refine continuous_pi fun x => ?_
  unfold glue
  cases (splitEquiv hnk).symm x with
  | inl p => exact (continuous_apply p).comp continuous_fst
  | inr p => exact (continuous_apply p).comp continuous_snd

/-- `glue` as a measurable equivalence. -/
def glueME (hnk : 0 < n + k) : ((HSite n k → ℝ) × (HSite n k → ℝ)) ≃ᵐ DField n k :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : HSite n k ⊕ HSite n k => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : DSite n k => ℝ) (splitEquiv hnk))

theorem glueME_apply (hnk : 0 < n + k) (z : (HSite n k → ℝ) × (HSite n k → ℝ)) :
    glueME hnk z = glue hnk z := by
  funext x
  obtain ⟨s, rfl⟩ := (splitEquiv hnk).surjective x
  simp only [glueME, MeasurableEquiv.trans_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rcases s with p | p
  · rw [glue_inl]; rfl
  · rw [glue_inr]; rfl

theorem glueME_mp (hnk : 0 < n + k) : MeasurePreserving (glueME hnk) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : DSite n k => ℝ) (splitEquiv hnk)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : HSite n k ⊕ HSite n k => ℝ))

/-- Change of variables φ = glue (ψ, η) (Lebesgue measure is preserved). -/
theorem integral_glue (hnk : 0 < n + k) (f : DField n k → ℝ) :
    ∫ φ, f φ = ∫ z : (HSite n k → ℝ) × (HSite n k → ℝ), f (glue hnk z) := by
  rw [← (glueME_mp hnk).integral_comp' f]
  simp only [glueME_apply]

/-! ### The reflection -/

/-- The bond reflection of the first coordinate, i ↦ N − 1 − i. -/
def reflX (x : DSite n k) : DSite n k := (Fin.rev x.1, x.2)

theorem reflX_inl (hnk : 0 < n + k) (p : HSite n k) :
    reflX (splitEquiv hnk (.inl p)) = splitEquiv hnk (.inr p) := by
  have := boxN_eq hnk; have := p.1.isLt
  refine Prod.ext (Fin.ext ?_) rfl
  simp only [reflX, splitEquiv_inl, splitEquiv_inr, Fin.val_rev]
  omega

theorem reflX_inr (hnk : 0 < n + k) (p : HSite n k) :
    reflX (splitEquiv hnk (.inr p)) = splitEquiv hnk (.inl p) := by
  have := boxN_eq hnk; have := p.1.isLt
  refine Prod.ext (Fin.ext ?_) rfl
  simp only [reflX, splitEquiv_inl, splitEquiv_inr, Fin.val_rev]
  omega

/-- Reflecting the glued field swaps the two halves. -/
theorem glue_reflX (hnk : 0 < n + k) (z : (HSite n k → ℝ) × (HSite n k → ℝ)) :
    (fun x => glue hnk z (reflX x)) = glue hnk (z.2, z.1) := by
  funext x
  obtain ⟨s, rfl⟩ := (splitEquiv hnk).surjective x
  rcases s with p | p
  · rw [reflX_inl, glue_inr, glue_inl]
  · rw [reflX_inr, glue_inl, glue_inr]

/-- F depends only on the field in the right half {x | N/2 ≤ x.1}. -/
def RightLocal (F : DField n k → ℝ) : Prop :=
  ∀ φ φ' : DField n k, (∀ x : DSite n k, halfN n k ≤ (x.1 : ℕ) → φ x = φ' x) → F φ = F φ'

theorem glue_right (hnk : 0 < n + k) {F : DField n k → ℝ} (hF : RightLocal F)
    (ψ η : HSite n k → ℝ) : F (glue hnk (ψ, η)) = F (glue hnk (ψ, 0)) := by
  refine hF _ _ fun x hx => ?_
  obtain ⟨s, rfl⟩ := (splitEquiv hnk).surjective x
  rcases s with p | p
  · simp
  · exfalso
    rw [splitEquiv_inr] at hx
    have := p.1.isLt
    have := halfN_pos hnk
    simp only at hx
    omega

/-! ### The coupling matrix in closed form -/

/-- Horizontal bonds: x = y + e₁. -/
def JHd (x y : DSite n k) : ℝ := if (x.1 : ℕ) = y.1 + 1 ∧ (x.2 : ℕ) = y.2 then 1 else 0

/-- Vertical bonds: x = y + e₂. -/
def JVd (x y : DSite n k) : ℝ := if (x.1 : ℕ) = y.1 ∧ (x.2 : ℕ) = y.2 + 1 then 1 else 0

/-- **Closed form of `Jnn`**: Jnn x y = [x = y + e₁] + [x = y + e₂]. -/
theorem Jnn_closed (x y : DSite n k) : Jnn n k x y = JHd x y + JVd x y := by
  have hy1 := y.1.isLt
  have hy2 := y.2.isLt
  have hx1 := x.1.isLt
  have hx2 := x.2.isLt
  unfold Jnn
  rw [Finset.sum_eq_single (((y.1 : ℕ) : ℤ), ((y.2 : ℕ) : ℤ))]
  · simp only [delta, ite_true, mul_one, JHd, JVd, Prod.mk.injEq]
    congr 1
    · by_cases h : (x.1 : ℕ) = y.1 + 1 ∧ (x.2 : ℕ) = y.2
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
    · by_cases h : (x.1 : ℕ) = y.1 ∧ (x.2 : ℕ) = y.2 + 1
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
  · intro p _ hp
    simp [delta, hp]
  · intro hp
    exfalso; apply hp
    simp only [boxIdx, Finset.mem_product, Finset.mem_Icc]
    omega

/-- The half-box coupling: [p = q + e₁] + [p = q + e₂] in the (distance, column) coordinates. -/
def hJ (p q : HSite n k) : ℝ :=
  (if (p.1 : ℕ) = q.1 + 1 ∧ (p.2 : ℕ) = q.2 then 1 else 0)
    + (if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 + 1 then 1 else 0)

/-- The half-box quadratic form Σ_{p,q} hJ p q ψ_p ψ_q. -/
def halfQ (ψ : HSite n k → ℝ) : ℝ := ∑ p, ∑ q, hJ p q * ψ p * ψ q

theorem Jnn_inl_inl (hnk : 0 < n + k) (p q : HSite n k) :
    Jnn n k (splitEquiv hnk (.inl p)) (splitEquiv hnk (.inl q)) = hJ p q := by
  rw [Jnn_closed, JHd, JVd, hJ, splitEquiv_inl, splitEquiv_inl]
  simp only
  congr 1
  · by_cases h : (p.1 : ℕ) = q.1 + 1 ∧ (p.2 : ℕ) = q.2
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  · by_cases h : (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]

theorem Jnn_inr_inr (hnk : 0 < n + k) (p q : HSite n k) :
    Jnn n k (splitEquiv hnk (.inr p)) (splitEquiv hnk (.inr q)) =
      (if (q.1 : ℕ) = p.1 + 1 ∧ (q.2 : ℕ) = p.2 then 1 else 0)
        + (if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 + 1 then 1 else 0) := by
  have := p.1.isLt; have := q.1.isLt
  rw [Jnn_closed, JHd, JVd, splitEquiv_inr, splitEquiv_inr]
  simp only
  congr 1
  · by_cases h : (q.1 : ℕ) = p.1 + 1 ∧ (q.2 : ℕ) = p.2
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  · by_cases h : (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]

theorem Jnn_inl_inr (hnk : 0 < n + k) (p q : HSite n k) :
    Jnn n k (splitEquiv hnk (.inl p)) (splitEquiv hnk (.inr q)) =
      if (p.1 : ℕ) = 0 ∧ (q.1 : ℕ) = 0 ∧ p.2 = q.2 then 1 else 0 := by
  have := p.1.isLt; have := q.1.isLt
  rw [Jnn_closed, JHd, JVd, splitEquiv_inl, splitEquiv_inr]
  simp only
  have hv : ¬ (halfN n k + (p.1 : ℕ) = halfN n k - 1 - q.1 ∧ (p.2 : ℕ) = q.2 + 1) := by omega
  rw [ite_eq_right hv, add_zero]
  by_cases h : (p.1 : ℕ) = 0 ∧ (q.1 : ℕ) = 0 ∧ p.2 = q.2
  · rw [ite_eq_left (by rw [h.2.2]; omega), ite_eq_left h]
  · rw [ite_eq_right (by rw [Fin.ext_iff] at h; omega), ite_eq_right h]

theorem Jnn_inr_inl (hnk : 0 < n + k) (p q : HSite n k) :
    Jnn n k (splitEquiv hnk (.inr p)) (splitEquiv hnk (.inl q)) = 0 := by
  have := p.1.isLt; have := q.1.isLt
  rw [Jnn_closed, JHd, JVd, splitEquiv_inr, splitEquiv_inl]
  simp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

/-- The boundary column of a half box: c j = (0, j), the sites adjacent to the plane. -/
def bnd (hnk : 0 < n + k) (j : Fin (boxN n k)) : HSite n k := (⟨0, halfN_pos hnk⟩, j)

theorem cross_sum (hnk : 0 < n + k) (ψ η : HSite n k → ℝ) :
    ∑ p, ∑ q, (if (p.1 : ℕ) = 0 ∧ (q.1 : ℕ) = 0 ∧ p.2 = q.2 then (1 : ℝ) else 0) * ψ p * η q
      = bcoup (bnd hnk) ψ η := by
  have h1 : ∀ p : HSite n k,
      ∑ q, (if (p.1 : ℕ) = 0 ∧ (q.1 : ℕ) = 0 ∧ p.2 = q.2 then (1 : ℝ) else 0) * ψ p * η q
        = if (p.1 : ℕ) = 0 then ψ p * η p else 0 := by
    intro p
    rw [Finset.sum_eq_single p]
    · by_cases h : (p.1 : ℕ) = 0
      · simp [h]
      · simp [h]
    · intro q _ hqp
      rw [ite_eq_right, zero_mul, zero_mul]
      rintro ⟨h1, h2, h3⟩
      exact hqp (Prod.ext (Fin.ext (by omega)) h3.symm)
    · simp
  simp_rw [h1]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨0, halfN_pos hnk⟩ : Fin (halfN n k))]
  · simp [bcoup, bnd]
  · intro a _ ha
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    intro h; exact ha (Fin.ext h)
  · simp

theorem halfQ_swap (η : HSite n k → ℝ) :
    ∑ p : HSite n k, ∑ q : HSite n k,
      ((if (q.1 : ℕ) = p.1 + 1 ∧ (q.2 : ℕ) = p.2 then (1 : ℝ) else 0)
        + (if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 + 1 then 1 else 0)) * η p * η q = halfQ η := by
  unfold halfQ hJ
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- The nearest-neighbour quadratic form of the glued field. -/
theorem quad_glue (hnk : 0 < n + k) (ψ η : HSite n k → ℝ) :
    ∑ x, ∑ y, Jnn n k x y * glue hnk (ψ, η) x * glue hnk (ψ, η) y
      = halfQ ψ + halfQ η + bcoup (bnd hnk) ψ η := by
  rw [← (splitEquiv hnk).sum_comp]
  simp_rw [← (splitEquiv hnk).sum_comp (fun y => Jnn n k _ y * _ * glue hnk (ψ, η) y)]
  simp only [Fintype.sum_sum_type, glue_inl, glue_inr, Jnn_inl_inl, Jnn_inr_inr, Jnn_inl_inr,
    Jnn_inr_inl, zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  rw [halfQ_swap, cross_sum hnk]
  unfold halfQ
  ring

/-- The single-site weight (the same at every site, `siteWeight_eq`). -/
def sw (n : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (y : ℝ) : ℝ :=
  Real.exp (-((4 + spacing n ^ 2 * m₀ ^ 2) * y ^ 2) / 2
    - lam * spacing n ^ 2 * wickPoly P (freeVar n m₀) y)

/-- The half-box weight B(ψ) = exp(Σ hJ ψ ψ) · ∏ w(ψ). -/
def Bh (n k : ℕ) (m₀ lam : ℝ) (P : Polynomial ℝ) (ψ : HSite n k → ℝ) : ℝ :=
  Real.exp (halfQ ψ) * ∏ p, sw n m₀ lam P (ψ p)

theorem Bh_pos (m₀ lam : ℝ) (P : Polynomial ℝ) (ψ : HSite n k → ℝ) : 0 < Bh n k m₀ lam P ψ :=
  mul_pos (Real.exp_pos _) (Finset.prod_pos fun _ _ => Real.exp_pos _)

/-- **(a) The decomposition across the reflection plane**:
dweight(glue(ψ, η)) = B(ψ) · B(η) · exp(Σ_j ψ(0, j) η(0, j)),
the only bonds crossing the plane being the horizontal ones between columns N/2 − 1 and N/2,
with coupling +1. -/
theorem dweight_glue (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ) (ψ η : HSite n k → ℝ) :
    dweight n k m₀ lam P (glue hnk (ψ, η)) =
      Bh n k m₀ lam P ψ * Bh n k m₀ lam P η * Real.exp (bcoup (bnd hnk) ψ η) := by
  rw [dweight_eq_ferro, quad_glue]
  have hsite : ∏ x, siteWeight n k m₀ lam P x (glue hnk (ψ, η) x)
      = (∏ p, sw n m₀ lam P (ψ p)) * ∏ p, sw n m₀ lam P (η p) := by
    rw [← (splitEquiv hnk).prod_comp, Fintype.prod_sum_type]
    simp only [glue_inl, glue_inr, siteWeight_eq, sw]
  rw [hsite, Bh, Bh, Real.exp_add, Real.exp_add]
  ring

/-- Reflection invariance of the box weight. -/
theorem dweight_reflX (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ) (φ : DField n k) :
    dweight n k m₀ lam P (fun x => φ (reflX x)) = dweight n k m₀ lam P φ := by
  obtain ⟨z, rfl⟩ : ∃ z, glue hnk z = φ :=
    ⟨(glueME hnk).symm φ, by rw [← glueME_apply, MeasurableEquiv.apply_symm_apply]⟩
  rw [glue_reflX, dweight_glue, dweight_glue]
  have : bcoup (bnd hnk) z.2 z.1 = bcoup (bnd hnk) z.1 z.2 := by
    unfold bcoup; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this]; ring

/-! ### Reflection positivity -/

/-- **(b) Reflection positivity of the Dirichlet box weight, general form.** For F depending
only on the right half (`RightLocal`) and G(ψ) = F(glue(ψ, 0)) the induced half-box function,
if G · B · exp(Σ_j ψ(0, j)²/2) is integrable, then
∫ F(φ ∘ refl) · F(φ) · dweight(φ) dφ ≥ 0. -/
theorem rp_dweight (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ) {F : DField n k → ℝ}
    (hF : RightLocal F)
    (hint : Integrable fun ψ : HSite n k → ℝ =>
      F (glue hnk (ψ, 0)) * Bh n k m₀ lam P ψ * bexp (bnd hnk) ψ) :
    0 ≤ ∫ φ : DField n k, F (fun x => φ (reflX x)) * F φ * dweight n k m₀ lam P φ := by
  rw [integral_glue hnk]
  have heq : ∀ z : (HSite n k → ℝ) × (HSite n k → ℝ),
      F (fun x => glue hnk z (reflX x)) * F (glue hnk z) * dweight n k m₀ lam P (glue hnk z)
        = (F (glue hnk (z.1, 0)) * Bh n k m₀ lam P z.1)
          * (F (glue hnk (z.2, 0)) * Bh n k m₀ lam P z.2) * Real.exp (bcoup (bnd hnk) z.1 z.2) := by
    intro z
    rw [glue_reflX, glue_right hnk hF z.2 z.1, show z = (z.1, z.2) from rfl,
      glue_right hnk hF z.1 z.2, dweight_glue]
    ring
  simp_rw [heq]
  exact rp_kernel (bnd hnk) (fun ψ => F (glue hnk (ψ, 0)) * Bh n k m₀ lam P ψ) hint

/-! ### Bounded observables: the integrability hypothesis discharged -/

/-- (B(ψ) · exp(Σ_j ψ(0, j)²/2))² = dweight(glue(ψ, ψ)). -/
theorem Bh_bexp_sq (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ) (ψ : HSite n k → ℝ) :
    (Bh n k m₀ lam P ψ * bexp (bnd hnk) ψ) ^ 2 = dweight n k m₀ lam P (glue hnk (ψ, ψ)) := by
  rw [dweight_glue, mul_pow, sq (bexp _ _), bexp, ← Real.exp_add]
  have : ∑ j, ψ (bnd hnk j) ^ 2 / 2 + ∑ j, ψ (bnd hnk j) ^ 2 / 2 = bcoup (bnd hnk) ψ ψ := by
    unfold bcoup; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

theorem Bh_bexp_eq (hnk : 0 < n + k) (m₀ lam : ℝ) (P : Polynomial ℝ) (ψ : HSite n k → ℝ) :
    Bh n k m₀ lam P ψ * bexp (bnd hnk) ψ
      = Real.sqrt (dweight n k m₀ lam P (glue hnk (ψ, ψ))) := by
  rw [← Bh_bexp_sq, Real.sqrt_sq (mul_pos (Bh_pos _ _ _ _) (bexp_pos _ _)).le]

/-- The Gaussian majorant on a half box. -/
def hgauss (n k : ℕ) (m₀ : ℝ) (ψ : HSite n k → ℝ) : ℝ :=
  ∏ p, Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * ψ p ^ 2)

theorem dgauss_glue (hnk : 0 < n + k) (m₀ : ℝ) (ψ : HSite n k → ℝ) :
    dgauss n k m₀ (glue hnk (ψ, ψ)) = hgauss n k m₀ ψ ^ 2 := by
  rw [dgauss, ← (splitEquiv hnk).prod_comp, Fintype.prod_sum_type]
  simp only [glue_inl, glue_inr]
  rw [hgauss]; ring

theorem integrable_hgauss {m₀ : ℝ} (hm : m₀ ≠ 0) : Integrable (hgauss n k m₀) := by
  have hb : 0 < m₀ ^ 2 * spacing n ^ 2 / 2 := by
    have := PP2Target.spacing_pos n
    positivity
  exact Integrable.fintype_prod (ι := HSite n k) (E := ℝ) (𝕜 := ℝ)
    (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ y => Real.exp (-(m₀ ^ 2 * spacing n ^ 2 / 2) * y ^ 2))
    (fun _ => integrable_exp_neg_mul_sq hb)

/-- The constant of `dweight_le`. -/
def wconst (n k : ℕ) (m₀ lam : ℝ) : ℝ :=
  Real.exp (lam * spacing n ^ 2 * (Fintype.card (DSite n k) * (6 * freeVar n m₀ ^ 2)))

theorem Bh_bexp_le (hnk : 0 < n + k) (m₀ lam : ℝ) (hlam : 0 ≤ lam) (ψ : HSite n k → ℝ) :
    Bh n k m₀ lam (Polynomial.X ^ 4) ψ * bexp (bnd hnk) ψ
      ≤ Real.sqrt (wconst n k m₀ lam) * hgauss n k m₀ ψ := by
  rw [Bh_bexp_eq]
  calc Real.sqrt (dweight n k m₀ lam (Polynomial.X ^ 4) (glue hnk (ψ, ψ)))
      ≤ Real.sqrt (wconst n k m₀ lam * dgauss n k m₀ (glue hnk (ψ, ψ))) :=
        Real.sqrt_le_sqrt (dweight_le m₀ lam hlam _)
    _ = Real.sqrt (wconst n k m₀ lam) * hgauss n k m₀ ψ := by
        rw [dgauss_glue, Real.sqrt_mul (show 0 ≤ wconst n k m₀ lam from (Real.exp_pos _).le),
          Real.sqrt_sq (show 0 ≤ hgauss n k m₀ ψ from
            Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]

/-- **Reflection positivity for bounded measurable right-half observables** (quartic model,
m₀ ≠ 0, λ ≥ 0): ∫ F(φ ∘ refl) · F(φ) · dweight(φ) dφ ≥ 0. -/
theorem rp_dweight_bounded (hnk : 0 < n + k) {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F : DField n k → ℝ} (hF : RightLocal F) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ φ, |F φ| ≤ C) :
    0 ≤ ∫ φ : DField n k,
      F (fun x => φ (reflX x)) * F φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  refine rp_dweight hnk m₀ lam _ hF ?_
  have h1 : Measurable fun ψ : HSite n k → ℝ => F (glue hnk (ψ, 0)) :=
    hFm.comp ((continuous_glue hnk).comp (continuous_id.prodMk continuous_const)).measurable
  have h2 : Continuous fun ψ : HSite n k → ℝ =>
      Real.sqrt (dweight n k m₀ lam (Polynomial.X ^ 4) (glue hnk (ψ, ψ))) :=
    Real.continuous_sqrt.comp ((continuous_dweight m₀ lam _).comp
      ((continuous_glue hnk).comp (continuous_id.prodMk continuous_id)))
  have hmeas : AEStronglyMeasurable fun ψ : HSite n k → ℝ =>
      F (glue hnk (ψ, 0)) * Bh n k m₀ lam (Polynomial.X ^ 4) ψ * bexp (bnd hnk) ψ := by
    refine (h1.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun ψ => ?_)
    simp only [Pi.mul_apply]
    rw [mul_assoc, Bh_bexp_eq]
  refine Integrable.mono' ((integrable_hgauss hm).const_mul
    (C * Real.sqrt (wconst n k m₀ lam))) hmeas (Filter.Eventually.of_forall fun ψ => ?_)
  rw [Real.norm_eq_abs, mul_assoc, abs_mul,
    abs_of_pos (mul_pos (Bh_pos _ _ _ _) (bexp_pos _ _))]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  calc |F (glue hnk (ψ, 0))| * (Bh n k m₀ lam (Polynomial.X ^ 4) ψ * bexp (bnd hnk) ψ)
      ≤ C * (Real.sqrt (wconst n k m₀ lam) * hgauss n k m₀ ψ) :=
        mul_le_mul (hC _) (Bh_bexp_le hnk m₀ lam hlam ψ)
          (mul_pos (Bh_pos _ _ _ _) (bexp_pos _ _)).le hC0
    _ = _ := by ring

/-- For bounded measurable F (m₀ ≠ 0, λ ≥ 0) the RP integrand is integrable, so the inequality
of `rp_dweight_bounded` is about a genuine (not junk-zero) Bochner integral. -/
theorem integrable_rp_integrand {m₀ : ℝ} (hm : m₀ ≠ 0) {lam : ℝ} (hlam : 0 ≤ lam)
    {F : DField n k → ℝ} (hFm : Measurable F) {C : ℝ} (hC : ∀ φ, |F φ| ≤ C) :
    Integrable fun φ : DField n k =>
      F (fun x => φ (reflX x)) * F φ * dweight n k m₀ lam (Polynomial.X ^ 4) φ := by
  have hr : Measurable fun φ : DField n k => F (fun x => φ (reflX x)) :=
    hFm.comp (continuous_pi fun x => continuous_apply (reflX x)).measurable
  refine Integrable.mono' ((integrable_dweight hm hlam).const_mul (C * C))
    ((hr.mul hFm).aestronglyMeasurable.mul
      (continuous_dweight m₀ lam _).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun φ => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hw : 0 < dweight n k m₀ lam (Polynomial.X ^ 4) φ := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw]
  have := mul_le_mul (hC (fun x => φ (reflX x))) (hC φ) (abs_nonneg _) hC0
  nlinarith [abs_nonneg (F (fun x => φ (reflX x))), abs_nonneg (F φ)]

end Lattice

end PP2RP
