import Mathlib

/-!
Yang-Mills table, Long Table (othermindset.com). Claude council, Session 4, 21 Nov 2026 (route lead B).
The spectral step of the bridge (companion foundation post "the spectral step of the bridge without the
spectral theorem", Lemmas 1 and 2), lattice only.

FORMALIZED.
* `YMSpectral.spectral_step` (Lemma 1): E is a real or complex Hilbert space (`RCLike 𝕜`, complete inner
  product space), T : E →L[𝕜] E is self-adjoint, α ≥ 0, D ⊆ E is dense, and for every v ∈ D there is a
  real K with re⟪v, T^(2n) v⟫ ≤ K·α^(2n) for all n ≥ 1. Then ‖T u‖ ≤ α‖u‖ for every u ∈ E.
  `spectral_step_opNorm`: the same hypotheses give ‖T‖ ≤ α (operator norm).
  The proof follows the paper: a_n = ‖Tⁿv‖² = re⟪v, T^(2n)v⟫; Cauchy-Schwarz gives a_(n+1)² ≤ a_n·a_(n+2);
  hence (ratios nondecreasing, in the multiplied-out form a₁·a_(n+1) ≤ a₀·a_(n+2), valid also when some
  a_n = 0) a₁^(n+1) ≤ a₀^n·a_(n+1); then a₀·a₁^m ≤ K·(α²a₀)^m for all m ≥ 1, which forces a₁ ≤ α²a₀
  (the paper's n-th root limit is replaced by: r^m ≤ K/a₀ for all m is impossible when r > 1);
  finally density, since {u : ‖Tu‖ ≤ α‖u‖} is closed.
* `YMSpectral.spectrum_subset_of_norm_le` (Lemma 2, first part, complex case): T self-adjoint on a complex
  Hilbert space and ‖T‖ ≤ α imply spectrum ℂ T ⊆ {z : Im z = 0, |Re z| ≤ α}.
  `YMSpectral.spectrum_subset_of_pos` (Lemma 2, second part): if also re⟪u, T u⟫ ≥ 0 for all u, then
  spectrum ℂ T ⊆ {z : Im z = 0, 0 ≤ Re z ≤ α}.
  Here `spectrum ℂ T` is Mathlib's spectrum in the Banach algebra E →L[ℂ] E: λ is outside it iff
  T − λ has a two-sided inverse in E →L[ℂ] E, i.e. a bounded inverse.
* `YMSpectral.bridge_spectral_step`: Lemma 1 and Lemma 2 combined (complex, T ≥ 0): the decay hypothesis
  on a dense set gives ‖T‖ ≤ α and spectrum ℂ T ⊆ [0, α].

NOT formalized. Lemma 2 is NOT proved by the paper's elementary argument (Neumann series, bounded below,
projection theorem): its Lean proof uses Mathlib's library (spectrum of a self-adjoint element of a
C*-algebra is real; ‖λ‖ ≤ ‖T‖ on the spectrum; spectrum of a positive operator is nonnegative). Only the
statements match. Nothing of the Corollary is formalized: not the Osterwalder-Schrader space, the
transfer operator, the decay bound (b), the density (c), reflection positivity (d), nor the restriction
to the orthogonal complement of the vacuum. Lemma 1 here is the abstract operator statement only.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open scoped InnerProductSpace
open RCLike

namespace YMSpectral
/-- Multiplicative form of "the ratios a(n+1)/a(n) are nondecreasing", from log-convexity. -/
theorem ratio_mono (a : ℕ → ℝ) (h0 : ∀ n, 0 ≤ a n)
    (h : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2)) :
    ∀ n, a 1 * a (n + 1) ≤ a 0 * a (n + 2) := by
  intro n
  induction n with
  | zero => simpa [sq] using h 0
  | succ n ih =>
    have hc := h (n + 1)
    have key : a (n + 2) * (a 1 * a (n + 2)) ≤ a (n + 2) * (a 0 * a (n + 3)) := by
      have e1 : a (n + 2) * (a 1 * a (n + 2)) = a 1 * a (n + 1 + 1) ^ 2 := by ring
      have e2 : a 1 * (a (n + 1) * a (n + 1 + 2)) = (a 1 * a (n + 1)) * a (n + 3) := by ring
      calc a (n + 2) * (a 1 * a (n + 2)) = a 1 * a (n + 1 + 1) ^ 2 := e1
        _ ≤ a 1 * (a (n + 1) * a (n + 1 + 2)) := mul_le_mul_of_nonneg_left hc (h0 1)
        _ = (a 1 * a (n + 1)) * a (n + 3) := e2
        _ ≤ (a 0 * a (n + 2)) * a (n + 3) := mul_le_mul_of_nonneg_right ih (h0 _)
        _ = a (n + 2) * (a 0 * a (n + 3)) := by ring
    rcases (h0 (n + 2)).lt_or_eq with hp | hz
    · exact le_of_mul_le_mul_left key hp
    · rw [← hz, mul_zero]; exact mul_nonneg (h0 0) (h0 _)

/-- Consequence: a(1)^(n+1) ≤ a(0)^n · a(n+1). -/
theorem pow_le (a : ℕ → ℝ) (h0 : ∀ n, 0 ≤ a n)
    (h : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2)) :
    ∀ n, a 1 ^ (n + 1) ≤ a 0 ^ n * a (n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc a 1 ^ (n + 1 + 1) = a 1 * a 1 ^ (n + 1) := by ring
      _ ≤ a 1 * (a 0 ^ n * a (n + 1)) := mul_le_mul_of_nonneg_left ih (h0 1)
      _ = a 0 ^ n * (a 1 * a (n + 1)) := by ring
      _ ≤ a 0 ^ n * (a 0 * a (n + 2)) :=
          mul_le_mul_of_nonneg_left (ratio_mono a h0 h n) (pow_nonneg (h0 0) n)
      _ = a 0 ^ (n + 1) * a (n + 1 + 1) := by ring

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

theorem re_inner_pow_two_mul {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (v : E) (n : ℕ) :
    re ⟪v, (T ^ (2 * n)) v⟫_𝕜 = ‖(T ^ n) v‖ ^ 2 := by
  have hs := (hT.pow n).isSymmetric
  have e : (T ^ (2 * n)) v = (T ^ n) ((T ^ n) v) := by
    rw [two_mul, pow_add]; rfl
  rw [e, ← inner_self_eq_norm_sq (𝕜 := 𝕜)]
  congr 1
  exact (hs v ((T ^ n) v)).symm

theorem log_convex {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (v : E) (n : ℕ) :
    (‖(T ^ (n + 1)) v‖ ^ 2) ^ 2 ≤ ‖(T ^ n) v‖ ^ 2 * ‖(T ^ (n + 2)) v‖ ^ 2 := by
  have hs := hT.isSymmetric
  set w := (T ^ n) v
  have e1 : (T ^ (n + 1)) v = T w := by
    rw [pow_succ']; rfl
  have e2 : (T ^ (n + 2)) v = T (T w) := by
    rw [show n + 2 = (n + 1) + 1 by ring, pow_succ']
    show T ((T ^ (n + 1)) v) = _
    rw [e1]
  rw [e1, e2]
  have cs : ‖T w‖ ^ 2 ≤ ‖w‖ * ‖T (T w)‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜)]
    have : ⟪T w, T w⟫_𝕜 = ⟪w, T (T w)⟫_𝕜 := hs w (T w)
    rw [this]
    exact re_inner_le_norm _ _
  have hn : 0 ≤ ‖T w‖ ^ 2 := by positivity
  calc (‖T w‖ ^ 2) ^ 2 ≤ (‖w‖ * ‖T (T w)‖) ^ 2 := pow_le_pow_left₀ hn cs 2
    _ = ‖w‖ ^ 2 * ‖T (T w)‖ ^ 2 := by ring

/-- **Lemma 1 (spectral step).** -/
theorem spectral_step (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (α : ℝ) (hα : 0 ≤ α)
    (D : Set E) (hD : Dense D)
    (hdecay : ∀ v ∈ D, ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → re ⟪v, (T ^ (2 * n)) v⟫_𝕜 ≤ K * α ^ (2 * n)) :
    ∀ u : E, ‖T u‖ ≤ α * ‖u‖ := by
  -- Step 1: the bound on D.
  have hDb : ∀ v ∈ D, ‖T v‖ ≤ α * ‖v‖ := by
    intro v hv
    obtain ⟨K, hK⟩ := hdecay v hv
    set a : ℕ → ℝ := fun n => ‖(T ^ n) v‖ ^ 2 with ha
    have h0 : ∀ n, 0 ≤ a n := fun n => by positivity
    have hlc : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2) := fun n => log_convex hT v n
    have hp := pow_le a h0 hlc
    have a0 : a 0 = ‖v‖ ^ 2 := by simp [ha]
    have a1 : a 1 = ‖T v‖ ^ 2 := by simp [ha]
    -- a 0 * a 1 ^ m ≤ K * (α^2 * a 0)^m for m ≥ 1
    have hb : ∀ m : ℕ, a 0 * a 1 ^ (m + 1) ≤ K * (α ^ 2 * a 0) ^ (m + 1) := by
      intro m
      have h1 := hK (m + 1) (by omega)
      rw [re_inner_pow_two_mul hT] at h1
      have h2 : a (m + 1) ≤ K * α ^ (2 * (m + 1)) := h1
      calc a 0 * a 1 ^ (m + 1) ≤ a 0 * (a 0 ^ m * a (m + 1)) :=
            mul_le_mul_of_nonneg_left (hp m) (h0 0)
        _ = a 0 ^ (m + 1) * a (m + 1) := by ring
        _ ≤ a 0 ^ (m + 1) * (K * α ^ (2 * (m + 1))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (h0 0) _)
        _ = K * (α ^ 2 * a 0) ^ (m + 1) := by ring
    have key : a 1 ≤ α ^ 2 * a 0 := by
      by_contra hlt'
      have hlt := lt_of_not_ge hlt'
      set c := α ^ 2 * a 0 with hc
      have hc0 : 0 ≤ c := mul_nonneg (sq_nonneg α) (h0 0)
      have hpos0 : 0 < a 0 := by
        rcases (h0 0).lt_or_eq with h | h
        · exact h
        · exfalso
          have hv0 : v = 0 := by
            rw [a0] at h
            exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h.symm)
          have : a 1 = 0 := by rw [a1, hv0]; simp
          rw [this] at hlt
          exact absurd hlt (not_lt.mpr hc0)
      rcases hc0.lt_or_eq with hcp | hcz
      · -- r := a 1 / c > 1, and a 0 * r^(m+1) ≤ K for all m
        have hr : 1 < a 1 / c := by rw [lt_div_iff₀ hcp]; linarith
        obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (K / a 0) hr
        have hb' := hb m
        have hcm : 0 < c ^ (m + 1) := pow_pos hcp _
        have : a 0 * (a 1 / c) ^ (m + 1) ≤ K := by
          rw [div_pow, ← mul_div_assoc, div_le_iff₀ hcm]
          exact hb'
        have hrm : (a 1 / c) ^ m ≤ (a 1 / c) ^ (m + 1) :=
          pow_le_pow_right₀ hr.le (Nat.le_succ m)
        have : K / a 0 < (a 1 / c) ^ (m + 1) := lt_of_lt_of_le hm hrm
        rw [div_lt_iff₀ hpos0] at this
        linarith
      · have hb0 := hb 0
        rw [← hcz] at hb0 hlt
        simp at hb0
        have : 0 < a 0 * a 1 := mul_pos hpos0 hlt
        linarith
    rw [a0, a1] at key
    have : ‖T v‖ ^ 2 ≤ (α * ‖v‖) ^ 2 := by rw [mul_pow]; exact key
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hα (norm_nonneg _))
      (by norm_num : (2 : ℕ) ≠ 0)).mp this
  -- Step 2: density.
  have hcl : IsClosed {u : E | ‖T u‖ ≤ α * ‖u‖} :=
    isClosed_le (continuous_norm.comp T.continuous) (continuous_const.mul continuous_norm)
  have hsub : closure D ⊆ {u : E | ‖T u‖ ≤ α * ‖u‖} := hcl.closure_subset_iff.mpr hDb
  intro u
  exact hsub (hD.closure_eq ▸ Set.mem_univ u)

/-- Lemma 1, operator-norm form: ‖T‖ ≤ α. -/
theorem spectral_step_opNorm (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (α : ℝ) (hα : 0 ≤ α)
    (D : Set E) (hD : Dense D)
    (hdecay : ∀ v ∈ D, ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → re ⟪v, (T ^ (2 * n)) v⟫_𝕜 ≤ K * α ^ (2 * n)) :
    ‖T‖ ≤ α :=
  T.opNorm_le_bound hα (spectral_step T hT α hα D hD hdecay)


section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Lemma 2, first part.** Self-adjoint with ‖T‖ ≤ α: spectrum in the real interval [−α, α]. -/
theorem spectrum_subset_of_norm_le (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (α : ℝ)
    (hnorm : ‖T‖ ≤ α) :
    spectrum ℂ T ⊆ {z : ℂ | z.im = 0 ∧ |z.re| ≤ α} := by
  intro z hz
  have hre : z = (z.re : ℂ) := hT.mem_spectrum_eq_re hz
  have hn : ‖z‖ ≤ ‖T‖ :=
    quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℂ T hz)
  refine ⟨by rw [hre]; simp, ?_⟩
  have : ‖z‖ = |z.re| := by rw [hre]; simp
  linarith

/-- **Lemma 2, second part.** If also ⟨u, T u⟩ ≥ 0 for all u: spectrum in [0, α]. -/
theorem spectrum_subset_of_pos (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hpos : ∀ u : H, 0 ≤ re ⟪u, T u⟫_ℂ) (α : ℝ) (hnorm : ‖T‖ ≤ α) :
    spectrum ℂ T ⊆ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ α} := by
  intro z hz
  obtain ⟨him, hab⟩ := spectrum_subset_of_norm_le T hT α hnorm hz
  have hre : z = (z.re : ℂ) := hT.mem_spectrum_eq_re hz
  have hzR : z.re ∈ spectrum ℝ T := by
    apply spectrum.of_algebraMap_mem ℂ
    rw [Complex.coe_algebraMap, ← hre]; exact hz
  have hP : T.IsPositive := ContinuousLinearMap.isPositive_def'.mpr
    ⟨hT, fun x => by
      have := hpos x
      rw [inner_re_symm] at this
      exact this⟩
  have h0 : (0 : H →L[ℂ] H) ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr hP
  exact ⟨him, spectrum_nonneg_of_nonneg h0 hzR, le_trans (le_abs_self _) hab⟩

/-- Lemmas 1 and 2 together (complex, T ≥ 0): the decay hypothesis on a dense set gives ‖T‖ ≤ α
and spectrum ℂ T ⊆ [0, α]. -/
theorem bridge_spectral_step (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hpos : ∀ u : H, 0 ≤ re ⟪u, T u⟫_ℂ) (α : ℝ) (hα : 0 ≤ α) (D : Set H) (hD : Dense D)
    (hdecay : ∀ v ∈ D, ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → re ⟪v, (T ^ (2 * n)) v⟫_ℂ ≤ K * α ^ (2 * n)) :
    ‖T‖ ≤ α ∧ spectrum ℂ T ⊆ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ α} :=
  have h := spectral_step_opNorm T hT α hα D hD hdecay
  ⟨h, spectrum_subset_of_pos T hT hpos α h⟩

end Complex

end YMSpectral
