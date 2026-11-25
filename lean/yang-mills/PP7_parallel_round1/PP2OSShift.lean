import LongTable.PP2OSRecon

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Hamiltonian track H, session 4
(plan item P2, steps 2–4). Time-shift operators on the OS Hilbert space of session 3
(`PP2OSRecon`): definition on the pre-Hilbert space, contraction by the iterated Cauchy–Schwarz
argument, symmetry, semigroup law, extension to the completion as a self-adjoint contraction.
Generic functional analysis plus four pointwise identities for translations of test functions.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* Generic kernel shifts. For a PSD kernel `P : osr_Kernel ι`, an `oss_Shift P` is a family
  S : ℝ → ι → ι with S 0 = id, S (s + t) = S s ∘ S t (s, t ≥ 0), the symmetry
  K(S t i, j) = K(i, S t j) (t ≥ 0) and the bound ‖K i j‖ ≤ 1.
  - `oss_A Sh t` = `Finsupp.lmapDomain (S t)` on `osr_Pre P` (δ_i ↦ δ_(S t i)).
  - `oss_form_mapDomain_left/right`: ⟪A c, d⟫, ⟪c, A d⟫ are the forms of the shifted kernels.
  - `oss_A_symm`: ⟪A t c, d⟫ = ⟪c, A t d⟫; `oss_A_comp`: A s (A t c) = A (s + t) c;
    `oss_A_zero`: A 0 = id.
  - `oss_norm_form_le`: ‖⟪c, c⟫‖ ≤ (Σ_i |c_i|)² when ‖K‖ ≤ 1; hence `oss_norm_A_le`:
    ‖A t c‖ ≤ Σ_i |c_i| for every t ≥ 0 (uniformly in t).
  - `oss_iter` (real lemma): N ≥ 0, a_n² ≤ N a_(n+1), a_n ≤ M for all n ⇒ a_0 ≤ N
    (if a_0 > N then a_n ≥ N (a_0/N)^(2^n) is unbounded). With a_n = ‖A(2^n t) c‖, N = ‖c‖
    (a_n² = re⟪c, A(2^(n+1) t) c⟫ ≤ ‖c‖ a_(n+1) by symmetry + semigroup + Cauchy–Schwarz)
    this is the Glimm–Jaffe iterated Cauchy–Schwarz bound: `oss_A_contraction`:
    ‖A t c‖ ≤ ‖c‖ for t ≥ 0. In particular A t maps null vectors to null vectors
    (`oss_A_null`), so it is well defined on V/N; no separate quotient step is needed since
    the completion of the seminormed space already identifies null vectors.
  - `oss_T Sh t : osr_H P →L[ℂ] osr_H P` = completion of A(max t 0) (bounded by 1).
    `oss_T_coe`: T t [c] = [A t c] (t ≥ 0); `oss_T_contraction`: ‖T t x‖ ≤ ‖x‖;
    `oss_T_symm`, `oss_T_selfAdjoint` (`IsSelfAdjoint`); `oss_T_zero`: T 0 = 1;
    `oss_T_add`: T (s + t) = T s * T t (s, t ≥ 0); `oss_T_vec`: T t (vec i) = vec (S t i);
    `oss_T_inner_vec`: ⟪vec i, T t (vec j)⟫ = K(i, S t j).
* OS case. τ_t = `translate (timeShift t)`. `oss_tau_pos` (τ_t keeps positive time for t ≥ 0),
  `oss_tau_add`, `oss_tau_zero`, `oss_tau_sub` (linearity), `oss_reflect_tau`:
  Θ τ_t f = τ_(−t) Θ f. `oss_shift Z hZ htr hb : oss_Shift (osr_kernel Z hZ)` with
  S t f = τ_(max t 0) f. HYPOTHESES USED: `OSPositive Z`, time-translation invariance
  Z(τ_t h) = Z(h) for all real t and all h (`htr`), and ‖Z h‖ ≤ 1 (`hb`). The symmetry
  Z(τ_t g − Θf) = Z(g − Θτ_t f) needs only translation invariance and Θτ_t = τ_(−t)Θ;
  Hermiticity Z(−h) = conj Z(h) and Θ-invariance are NOT needed (Hermiticity of the form is
  already part of `OSPositive` in ComplexOrder, session 3 `osr_herm`).
  `oss_OST Z hZ htr hb t : OSHilbert Z hZ →L[ℂ] OSHilbert Z hZ`.
* `oss_OS_main`: for this T and ψ = `osr_psi Z hZ`, Ω = ψ 0:
  ‖Ω‖ = 1 (if Z 0 = 1), T t self-adjoint (t ≥ 0), T 0 = 1, T (s + t) = T s * T t (s, t ≥ 0),
  T t Ω = Ω (t ≥ 0), ⟪ψ f, T t (ψ g)⟫ = Z(τ_t g − Θf) (positive-time f, g, t ≥ 0),
  span ψ(positive-time) dense, ‖T t u‖ ≤ ‖u‖ for all u. That is every clause of `OSGap` except
  the gap clause, with density for positive-time (not yet compactly supported) test functions.

NOT formalized (remaining for S5).
* Density of span ψ(positive-time, compact support) (needs continuity of Z on Schwartz space,
  see session 3 header).
* The gap clause: ‖T t u‖ ≤ e^(−mt)‖u‖ on Ω^⊥ via `PP2Gap.semigroup_gap` from `ClustersAt Z m`
  (plan P3), and the `OSGap` assembly. All operator hypotheses of `semigroup_gap` (self-adjoint,
  semigroup on t ≥ 0, T Ω = Ω, Ω unit) are supplied by `oss_OS_main`.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2OSShift

open PP2OSRecon

/-! ## A real lemma: the iterated Cauchy–Schwarz bound -/

/-- If a_n² ≤ N a_(n+1) and a_n ≤ M for all n, then a_0 ≤ N. -/
theorem oss_iter (a : ℕ → ℝ) (N M : ℝ) (hN : 0 ≤ N)
    (hstep : ∀ n, a n ^ 2 ≤ N * a (n + 1)) (hM : ∀ n, a n ≤ M) : a 0 ≤ N := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  rcases hN.eq_or_lt with h0 | hpos
  · have := hstep 0
    rw [← h0, zero_mul] at this
    nlinarith
  set r := a 0 / N with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hpos]; linarith
  have hgrow : ∀ n, N * r ^ (2 ^ n) ≤ a n := by
    intro n
    induction n with
    | zero => simp [hr, mul_div_cancel₀ _ hpos.ne']
    | succ n ih =>
      have h1 : 0 ≤ N * r ^ (2 ^ n) := by positivity
      have h2 : (N * r ^ (2 ^ n)) ^ 2 ≤ a n ^ 2 := pow_le_pow_left₀ h1 ih 2
      have h3 : N * (N * r ^ (2 ^ (n + 1))) = (N * r ^ (2 ^ n)) ^ 2 := by
        rw [pow_succ, pow_mul]; ring
      have h4 : N * (N * r ^ (2 ^ (n + 1))) ≤ N * a (n + 1) := by
        rw [h3]; exact h2.trans (hstep n)
      exact le_of_mul_le_mul_left h4 hpos
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / N) hr1
  have h5 : r ^ n ≤ r ^ (2 ^ n) := pow_le_pow_right₀ hr1.le (Nat.lt_two_pow_self).le
  have h6 : N * r ^ (2 ^ n) ≤ M := (hgrow n).trans (hM n)
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

/-! ## Shifted kernels and push-forward of finitely supported combinations -/

section Generic

variable {ι : Type}

theorem oss_form_mapDomain_left (K : ι → ι → ℂ) (σ : ι → ι) (c d : ι →₀ ℂ) :
    osr_form K (Finsupp.mapDomain σ c) d = osr_form (fun i j => K (σ i) j) c d := by
  unfold osr_form
  rw [Finsupp.sum_mapDomain_index]
  · intro i; simp
  · intro i a₁ a₂
    rw [← Finsupp.sum_add]
    simp [add_mul]

theorem oss_form_mapDomain_right (K : ι → ι → ℂ) (σ : ι → ι) (c d : ι →₀ ℂ) :
    osr_form K c (Finsupp.mapDomain σ d) = osr_form (fun i j => K i (σ j)) c d := by
  unfold osr_form
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finsupp.sum_mapDomain_index]
  · intro j; simp
  · intro j b₁ b₂; ring

theorem oss_form_mapDomain_both (K : ι → ι → ℂ) (σ : ι → ι) (c : ι →₀ ℂ) :
    osr_form K (Finsupp.mapDomain σ c) (Finsupp.mapDomain σ c) =
      osr_form (fun i j => K (σ i) (σ j)) c c := by
  rw [oss_form_mapDomain_left, oss_form_mapDomain_right]

theorem oss_mapDomain_comp' (σ τ ρ : ι → ι) (h : ∀ i, ρ i = σ (τ i)) (c : ι →₀ ℂ) :
    Finsupp.mapDomain σ (Finsupp.mapDomain τ c) = Finsupp.mapDomain ρ c := by
  have : ρ = σ ∘ τ := funext h
  rw [this, Finsupp.mapDomain_comp]

theorem oss_mapDomain_id' (σ : ι → ι) (h : ∀ i, σ i = i) (c : ι →₀ ℂ) :
    Finsupp.mapDomain σ c = c := by
  have : σ = id := funext h
  rw [this, Finsupp.mapDomain_id]

/-- ‖⟪c, c⟫‖ ≤ (Σ_i |c_i|)² for a kernel bounded by 1. -/
theorem oss_norm_form_le (K : ι → ι → ℂ) (hK : ∀ i j, ‖K i j‖ ≤ 1) (c : ι →₀ ℂ) :
    ‖osr_form K c c‖ ≤ (c.sum fun _ a => ‖a‖) ^ 2 := by
  unfold osr_form Finsupp.sum
  calc ‖∑ i ∈ c.support, ∑ j ∈ c.support, conj (c i) * c j * K i j‖
      ≤ ∑ i ∈ c.support, ∑ j ∈ c.support, ‖c i‖ * ‖c j‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_of_le_one_right (by positivity) (hK i j)
    _ = (∑ i ∈ c.support, ‖c i‖) ^ 2 := by rw [sq, Finset.sum_mul_sum]

/-- A time-shift structure on the index set of a PSD kernel. -/
structure oss_Shift (P : osr_Kernel ι) where
  S : ℝ → ι → ι
  zero : ∀ i, S 0 i = i
  add : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ i, S (s + t) i = S s (S t i)
  symm : ∀ t, 0 ≤ t → ∀ i j, P.K (S t i) j = P.K i (S t j)
  bdd : ∀ i j, ‖P.K i j‖ ≤ 1

variable {P : osr_Kernel ι} (Sh : oss_Shift P)

/-- The shift on the pre-Hilbert space: δ_i ↦ δ_(S t i). -/
def oss_A (t : ℝ) : osr_Pre P →ₗ[ℂ] osr_Pre P := Finsupp.lmapDomain ℂ ℂ (Sh.S t)

theorem oss_A_apply (t : ℝ) (c : osr_Pre P) :
    oss_A Sh t c = (Finsupp.mapDomain (Sh.S t) (c : ι →₀ ℂ) : ι →₀ ℂ) := rfl

theorem oss_A_symm {t : ℝ} (ht : 0 ≤ t) (c d : osr_Pre P) :
    ⟪oss_A Sh t c, d⟫_ℂ = ⟪c, oss_A Sh t d⟫_ℂ := by
  show osr_form P.K (Finsupp.mapDomain (Sh.S t) c) d = osr_form P.K c (Finsupp.mapDomain (Sh.S t) d)
  exact (oss_form_mapDomain_left P.K (Sh.S t) c d).trans
    ((congrArg (fun K' => osr_form K' c d) (funext₂ (Sh.symm t ht))).trans
      (oss_form_mapDomain_right P.K (Sh.S t) c d).symm)

theorem oss_A_comp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (c : osr_Pre P) :
    oss_A Sh s (oss_A Sh t c) = oss_A Sh (s + t) c := by
  exact oss_mapDomain_comp' (Sh.S s) (Sh.S t) (Sh.S (s + t)) (Sh.add s t hs ht) c

theorem oss_A_zero (c : osr_Pre P) : oss_A Sh 0 c = c := by
  exact oss_mapDomain_id' (Sh.S 0) Sh.zero c

theorem oss_norm_sq (c : osr_Pre P) : ‖c‖ ^ 2 = (osr_form P.K c c).re := by
  have h := @norm_sq_eq_re_inner ℂ (osr_Pre P) _ _ _ c
  rw [osr_inner_pre] at h
  simpa using h

/-- The shift is bounded by Σ_i |c_i|, uniformly in t. -/
theorem oss_norm_A_le (t : ℝ) (c : osr_Pre P) :
    ‖oss_A Sh t c‖ ≤ ((c : ι →₀ ℂ).sum fun _ a => ‖a‖) := by
  have h1 : ‖oss_A Sh t c‖ ^ 2 ≤ ((c : ι →₀ ℂ).sum fun _ a => ‖a‖) ^ 2 := by
    have e2 : osr_form P.K (oss_A Sh t c) (oss_A Sh t c) =
        osr_form (fun i j => P.K (Sh.S t i) (Sh.S t j)) c c :=
      oss_form_mapDomain_both P.K (Sh.S t) c
    calc ‖oss_A Sh t c‖ ^ 2 = (osr_form P.K (oss_A Sh t c) (oss_A Sh t c)).re := oss_norm_sq _
      _ = (osr_form (fun i j => P.K (Sh.S t i) (Sh.S t j)) c c).re := congrArg Complex.re e2
      _ ≤ ‖osr_form (fun i j => P.K (Sh.S t i) (Sh.S t j)) c c‖ := Complex.re_le_norm _
      _ ≤ _ := oss_norm_form_le _ (fun i j => Sh.bdd _ _) c
  have h2 : 0 ≤ ((c : ι →₀ ℂ).sum fun _ a => ‖a‖) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  nlinarith [norm_nonneg (oss_A Sh t c)]

/-- ‖A u c‖² ≤ ‖c‖ ‖A (2u) c‖ (symmetry, semigroup, Cauchy–Schwarz). -/
theorem oss_A_sq_le {u : ℝ} (hu : 0 ≤ u) (c : osr_Pre P) :
    ‖oss_A Sh u c‖ ^ 2 ≤ ‖c‖ * ‖oss_A Sh (u + u) c‖ := by
  have h := @norm_sq_eq_re_inner ℂ (osr_Pre P) _ _ _ (oss_A Sh u c)
  rw [h, oss_A_symm Sh hu, oss_A_comp Sh hu hu]
  exact re_inner_le_norm _ _

/-- **Contraction** (Glimm–Jaffe iterated Cauchy–Schwarz): ‖A t c‖ ≤ ‖c‖ for t ≥ 0. -/
theorem oss_A_contraction {t : ℝ} (ht : 0 ≤ t) (c : osr_Pre P) : ‖oss_A Sh t c‖ ≤ ‖c‖ := by
  have key := oss_iter (fun n => ‖oss_A Sh (2 ^ n * t) c‖) ‖c‖
    ((c : ι →₀ ℂ).sum fun _ a => ‖a‖) (norm_nonneg _)
    (fun n => by
      have e : (2 : ℝ) ^ (n + 1) * t = 2 ^ n * t + 2 ^ n * t := by rw [pow_succ]; ring
      show ‖oss_A Sh (2 ^ n * t) c‖ ^ 2 ≤ ‖c‖ * ‖oss_A Sh (2 ^ (n + 1) * t) c‖
      rw [e]
      exact oss_A_sq_le Sh (by positivity) c)
    (fun n => oss_norm_A_le Sh _ c)
  simpa using key

/-- The shift maps null vectors to null vectors (so it is well defined on V/N). -/
theorem oss_A_null {t : ℝ} (ht : 0 ≤ t) (c : osr_Pre P) (hc : (osr_form P.K c c).re = 0) :
    (osr_form P.K (oss_A Sh t c) (oss_A Sh t c)).re = 0 := by
  have h1 := oss_A_contraction Sh ht c
  have h2 : ‖c‖ = 0 := by
    have := oss_norm_sq c
    rw [hc] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  rw [← oss_norm_sq]
  have : ‖oss_A Sh t c‖ = 0 := le_antisymm (h2 ▸ h1) (norm_nonneg _)
  rw [this]; ring

/-- The shift as a continuous linear map of norm ≤ 1 (at time max t 0). -/
def oss_Acl (t : ℝ) : osr_Pre P →L[ℂ] osr_Pre P :=
  (oss_A Sh (max t 0)).mkContinuous 1 fun c => by
    rw [one_mul]; exact oss_A_contraction Sh (le_max_right t 0) c

/-- The time-shift operator on the OS Hilbert space (t ≥ 0; T t = T 0 = 1 for t < 0). -/
def oss_T (t : ℝ) : osr_H P →L[ℂ] osr_H P := (oss_Acl Sh t).completion

theorem oss_T_coe {t : ℝ} (ht : 0 ≤ t) (c : osr_Pre P) :
    oss_T Sh t (c : osr_H P) = ((oss_A Sh t c : osr_Pre P) : osr_H P) := by
  rw [oss_T, ContinuousLinearMap.completion_apply_coe, oss_Acl, LinearMap.mkContinuous_apply,
    max_eq_left ht]

theorem oss_T_contraction (t : ℝ) (x : osr_H P) : ‖oss_T Sh t x‖ ≤ ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le ((oss_T Sh t).continuous.norm) continuous_norm
  | ih c =>
    rw [oss_T, ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, oss_Acl, LinearMap.mkContinuous_apply]
    exact oss_A_contraction Sh (le_max_right t 0) c

theorem oss_T_symm {t : ℝ} (ht : 0 ≤ t) (x y : osr_H P) :
    ⟪oss_T Sh t x, y⟫_ℂ = ⟪x, oss_T Sh t y⟫_ℂ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih c =>
    induction y using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih d =>
      rw [oss_T_coe Sh ht, oss_T_coe Sh ht, UniformSpace.Completion.inner_coe,
        UniformSpace.Completion.inner_coe, oss_A_symm Sh ht]

theorem oss_T_selfAdjoint {t : ℝ} (ht : 0 ≤ t) : IsSelfAdjoint (oss_T Sh t) :=
  LinearMap.IsSymmetric.isSelfAdjoint fun x y => oss_T_symm Sh ht x y

theorem oss_T_zero : oss_T Sh 0 = 1 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (oss_T Sh 0).continuous continuous_id
  | ih c =>
    rw [oss_T_coe Sh le_rfl, oss_A_zero]; rfl

theorem oss_T_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    oss_T Sh (s + t) = oss_T Sh s * oss_T Sh t := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (oss_T Sh (s + t)).continuous (oss_T Sh s * oss_T Sh t).continuous
  | ih c =>
    rw [show (oss_T Sh s * oss_T Sh t) (c : osr_H P) = oss_T Sh s (oss_T Sh t c) from rfl, oss_T_coe Sh (add_nonneg hs ht), oss_T_coe Sh ht,
      oss_T_coe Sh hs, oss_A_comp Sh hs ht]

theorem oss_T_vec {t : ℝ} (ht : 0 ≤ t) (i : ι) : oss_T Sh t (osr_vec P i) = osr_vec P (Sh.S t i) := by
  rw [osr_vec, osr_vec, oss_T_coe Sh ht]
  congr 1
  rw [oss_A_apply]
  exact Finsupp.mapDomain_single

theorem oss_T_inner_vec {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    ⟪osr_vec P i, oss_T Sh t (osr_vec P j)⟫_ℂ = P.K i (Sh.S t j) := by
  rw [oss_T_vec Sh ht, osr_inner_vec]

end Generic

/-! ## The OS case: time translations of test functions -/

section OS

open PP2Target PP2RP2

/-- τ_t f = f(· − (t, 0)). -/
abbrev oss_tau (t : ℝ) (f : TestFn) : TestFn := PP2Target.translate (timeShift t) f

theorem oss_tau_apply (t : ℝ) (f : TestFn) (x : Plane) :
    oss_tau t f x = f (x - timeShift t) := rfl

theorem oss_timeShift_add (s t : ℝ) : timeShift (s + t) = timeShift s + timeShift t := by
  ext i; fin_cases i <;> simp [timeShift]

theorem oss_tau_pos {t : ℝ} (ht : 0 ≤ t) {f : TestFn} (hf : PositiveTime f) :
    PositiveTime (oss_tau t f) := by
  intro x hx
  rw [oss_tau_apply] at hx
  have := hf _ hx
  simp [timeShift] at this
  linarith

theorem oss_tau_add (s t : ℝ) (f : TestFn) : oss_tau (s + t) f = oss_tau s (oss_tau t f) := by
  ext x
  rw [oss_tau_apply, oss_tau_apply, oss_tau_apply, oss_timeShift_add, sub_sub, add_comm]

theorem oss_tau_zero (f : TestFn) : oss_tau 0 f = f := by
  ext x
  rw [oss_tau_apply]
  congr 1
  ext i; fin_cases i <;> simp [timeShift]

theorem oss_tau_sub (t : ℝ) (f g : TestFn) : oss_tau t (f - g) = oss_tau t f - oss_tau t g := by
  unfold oss_tau PP2Target.translate
  exact map_sub _ _ _

theorem oss_reflect_tau (t : ℝ) (f : TestFn) :
    reflect (oss_tau t f) = oss_tau (-t) (reflect f) := by
  ext x
  rw [reflect_apply, oss_tau_apply, oss_tau_apply, reflect_apply]
  congr 1
  ext i; fin_cases i <;> simp [timeShift]; ring

/-- The shift on positive-time test functions, S t f = τ_(max t 0) f. -/
def oss_S (t : ℝ) (f : {f : TestFn // PositiveTime f}) : {f : TestFn // PositiveTime f} :=
  ⟨oss_tau (max t 0) f.1, oss_tau_pos (le_max_right t 0) f.2⟩

/-- The time-shift structure of a translation-invariant OS-positive Z with |Z| ≤ 1. -/
def oss_shift (Z : TestFn → ℂ) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (oss_tau t h) = Z h) (hb : ∀ h, ‖Z h‖ ≤ 1) :
    oss_Shift (osr_kernel Z hZ) where
  S := oss_S
  zero i := by
    apply Subtype.ext
    simp only [oss_S, max_self]
    exact oss_tau_zero _
  add s t hs ht i := by
    apply Subtype.ext
    simp only [oss_S, max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht)]
    exact oss_tau_add s t _
  symm t ht i j := by
    show Z (j.1 - reflect (oss_tau (max t 0) i.1)) = Z (oss_tau (max t 0) j.1 - reflect i.1)
    rw [max_eq_left ht, oss_reflect_tau, ← htr t, oss_tau_sub, ← oss_tau_add, add_neg_cancel,
      oss_tau_zero]
  bdd i j := hb _

/-- The OS time-shift operators T(t) on `OSHilbert Z hZ`. -/
def oss_OST (Z : TestFn → ℂ) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (oss_tau t h) = Z h) (hb : ∀ h, ‖Z h‖ ≤ 1) (t : ℝ) :
    OSHilbert Z hZ →L[ℂ] OSHilbert Z hZ :=
  oss_T (oss_shift Z hZ htr hb) t

theorem oss_psi_pos (Z : TestFn → ℂ) (hZ : OSPositive Z) {f : TestFn} (hf : PositiveTime f) :
    osr_psi Z hZ f = osr_vec (osr_kernel Z hZ) ⟨f, hf⟩ := by
  rw [osr_psi, dite_eq_left_of_eq_true (eq_true hf)]

/-- **Main theorem of the session.** Every clause of `OSGap` except the gap clause (and with
density for all positive-time test functions), plus the contraction bound. -/
theorem oss_OS_main (Z : TestFn → ℂ) (hZ : OSPositive Z)
    (htr : ∀ (t : ℝ) (h : TestFn), Z (PP2Target.translate (timeShift t) h) = Z h)
    (hb : ∀ h, ‖Z h‖ ≤ 1) (h0 : Z 0 = 1) :
    let T := oss_OST Z hZ htr hb
    let ψ := osr_psi Z hZ
    let Ω := ψ 0
    ‖Ω‖ = 1 ∧ (∀ t, 0 ≤ t → IsSelfAdjoint (T t)) ∧ T 0 = 1 ∧
    (∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) ∧
    (∀ t, 0 ≤ t → T t Ω = Ω) ∧
    (∀ f g, PositiveTime f → PositiveTime g → ∀ t, 0 ≤ t →
      ⟪ψ f, T t (ψ g)⟫_ℂ = Z (PP2Target.translate (timeShift t) g - reflect f)) ∧
    Dense ((Submodule.span ℂ (ψ '' {f | PositiveTime f})) : Set (OSHilbert Z hZ)) ∧
    (∀ t u, ‖T t u‖ ≤ ‖u‖) := by
  intro T ψ Ω
  refine ⟨osr_vacuum_norm Z hZ h0, fun t ht => oss_T_selfAdjoint _ ht, oss_T_zero _,
    fun s t hs ht => oss_T_add _ hs ht, fun t ht => ?_, fun f g hf hg t ht => ?_,
    osr_psi_dense Z hZ, fun t u => oss_T_contraction _ t u⟩
  · show oss_T _ t (osr_psi Z hZ 0) = osr_psi Z hZ 0
    rw [oss_psi_pos Z hZ positiveTime_zero, oss_T_vec _ ht]
    congr 1
  · show ⟪osr_psi Z hZ f, oss_T _ t (osr_psi Z hZ g)⟫_ℂ = _
    rw [oss_psi_pos Z hZ hf, oss_psi_pos Z hZ hg, oss_T_inner_vec _ ht]
    show Z (oss_tau (max t 0) g - reflect f) = _
    rw [max_eq_left ht]

end OS

end PP2OSShift
