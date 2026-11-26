import LongTable.PP2RP2

/-!
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction, Hamiltonian track H, session 3
(plan item P2, first half). Abstract Osterwalder–Schrader reconstruction of the Hilbert space
from a positive-semidefinite kernel, and its specialisation to an OS-positive functional
Z : TestFn → ℂ (`PP2RP2.OSPositive`). Generic functional analysis: no lattice, no model input.

FORMALIZED (no sorry; axioms propext, Classical.choice, Quot.sound).
* General kernel K : ι → ι → ℂ, `osr_PSD K`: 0 ≤ Σ_{a,b} conj(c_a) c_b K(x_a, x_b) for every finite
  family x : Fin m → ι, c : Fin m → ℂ (ComplexOrder: real and ≥ 0; the same shape as `OSPositive`).
  - `osr_herm`: a PSD kernel is automatically Hermitian, conj K(i, j) = K(j, i) (2×2 minors with
    c = (1, 1) and c = (1, i)). So NO separate Hermiticity hypothesis on Z is needed: `OSPositive`
    in ComplexOrder already contains it.
  - `osr_psd_finset`: the Fin-family form gives the Finset form.
* Pre-Hilbert space. `osr_Pre P` = ι →₀ ℂ (finitely supported formal combinations, `Finsupp`),
  `osr_form K c d = Σ_{i,j} conj(c_i) d_j K(i, j)` (conjugate-linear in the first slot, Mathlib's
  convention); `osr_form_conj`, `osr_form_add_left`, `osr_form_smul_left`, `osr_form_self_nonneg`;
  bundled as `osr_core P : PreInnerProductSpace.Core ℂ (osr_Pre P)`, giving a
  `SeminormedAddCommGroup` and an `InnerProductSpace ℂ` (`InnerProductSpace.ofCore`).
  `osr_inner_pre`: ⟪c, d⟫ = osr_form K c d (definitional).
* Null space. `osr_null_form`: re⟪c, c⟫ = 0 ⇒ ⟪c, d⟫ = 0 for all d (Cauchy–Schwarz);
  `osr_coe_eq_zero_iff`: the image of c in the Hilbert space is 0 iff re⟪c, c⟫ = 0. So the null
  space N = {c : ⟪c, c⟫ = 0} is exactly the kernel of V → H; the quotient V/N is not built by
  hand: `UniformSpace.Completion` of a SEMInormed inner-product space is already a (separated)
  Hilbert space (Mathlib: `UniformSpace.Completion.innerProductSpace`, normed by
  `Completion` of a seminormed group), and it factors through `SeparationQuotient` = V/N.
* Hilbert space. `osr_H P` = completion; complete, `InnerProductSpace ℂ`, `NormedAddCommGroup`.
  `osr_vec P i` = class of δ_i; `osr_inner_vec`: ⟪vec i, vec j⟫ = K(i, j);
  `osr_dense`: span(range vec) is dense in `osr_H P`.
* OS case. ι = {f : TestFn // PositiveTime f}, K(f, g) = Z(g − Θf), Θ = `reflect`.
  `osr_kernel Z hZ` from `OSPositive Z`; `OSHilbert Z hZ` (a `Type`, as `OSGap` needs);
  `osr_psi Z hZ : TestFn → OSHilbert` (class of δ_f for positive-time f, 0 otherwise);
  - `osr_psi_inner`: ⟪ψ f, ψ g⟫ = Z(g − Θf) for positive-time f, g (the t = 0 case of the
    `OSGap` matrix-element clause, same slot convention);
  - `osr_psi_dense`: span ψ(positive-time) is dense;
  - `osr_vacuum_norm`: Ω := ψ 0 has ‖Ω‖ = 1 when Z 0 = 1 (`positiveTime_zero`: 0 is positive-time).
  - `osr_kernel_herm_of`: the standard hypotheses Z(−h) = conj Z(h) and Z(Θh) = Z(h) also give
    Hermiticity of (f, g) ↦ Z(g − Θf) on ALL f, g (not needed above; recorded for P3/S4).

NOT formalized.
* Density in the form `OSGap` asks for: span ψ(f), f positive-time WITH COMPACT SUPPORT. With ι =
  all positive-time f this needs ψ f ∈ closure span ψ(compact): true if Z is continuous on
  Schwartz space (cut-offs χ(x/R) f → f in 𝒮 preserve positive time, and
  ‖ψ f − ψ g‖² = Z(f−Θf) − Z(g−Θf) − Z(f−Θg) + Z(g−Θg)). A continuity hypothesis on Z (E1 of
  the plan gives it for limit points) is therefore needed in S5; not done here.
* Time-shift operators T(t) (well-definedness on classes, iterated Cauchy–Schwarz contraction,
  self-adjointness, semigroup, extension to the completion): session S4.
* The gap clause (P3) and the `OSGap` assembly (S5).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PP2OSRecon

/-! ## Positive-semidefinite kernels -/

section Kernel

variable {ι : Type}

/-- Positive semidefiniteness of a kernel, in the Fin-family form of `OSPositive`. -/
def osr_PSD (K : ι → ι → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → ι) (c : Fin m → ℂ), 0 ≤ ∑ a, ∑ b, conj (c a) * c b * K (x a) (x b)

/-- A positive-semidefinite kernel (in `ComplexOrder`) is Hermitian. -/
theorem osr_herm {K : ι → ι → ℂ} (hK : osr_PSD K) (i j : ι) : conj (K i j) = K j i := by
  have h2 := hK 2 ![i, j] ![1, 1]
  have h3 := hK 2 ![i, j] ![1, Complex.I]
  have hi := hK 1 ![i] ![1]
  have hj := hK 1 ![j] ![1]
  simp [Fin.sum_univ_two, Complex.nonneg_iff] at h2 h3 hi hj
  apply Complex.ext <;> simp <;> linarith [h2.2, h3.2]

/-- The Finset form of positive semidefiniteness. -/
theorem osr_psd_finset {K : ι → ι → ℂ} (hK : osr_PSD K) (s : Finset ι) (c : ι → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * K i j := by
  have h1 : ∀ G : ι → ℂ, ∑ a : Fin s.card, G (s.equivFin.symm a) = ∑ i ∈ s, G i := by
    intro G
    rw [Equiv.sum_comp s.equivFin.symm (fun i : s => G i), Finset.sum_coe_sort]
  have h := hK s.card (fun a => (s.equivFin.symm a : ι)) (fun a => c (s.equivFin.symm a))
  rw [← h1]
  convert h using 2 with a
  exact (h1 (fun j => conj (c (s.equivFin.symm a)) * c j * K (s.equivFin.symm a) j)).symm

/-! ## The sesquilinear form on finitely supported combinations -/

/-- ⟪c, d⟫ = Σ_{i,j} conj(c_i) d_j K(i, j). -/
def osr_form (K : ι → ι → ℂ) (c d : ι →₀ ℂ) : ℂ :=
  c.sum fun i a => d.sum fun j b => conj a * b * K i j

theorem osr_form_add_left (K : ι → ι → ℂ) (c c' d : ι →₀ ℂ) :
    osr_form K (c + c') d = osr_form K c d + osr_form K c' d := by
  unfold osr_form
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i a₁ a₂
    rw [← Finsupp.sum_add]
    simp [add_mul]

theorem osr_form_smul_left (K : ι → ι → ℂ) (c d : ι →₀ ℂ) (r : ℂ) :
    osr_form K (r • c) d = conj r * osr_form K c d := by
  unfold osr_form
  rw [Finsupp.sum_smul_index' (by intro i; simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul, map_mul]
  ring

theorem osr_form_conj {K : ι → ι → ℂ} (hK : osr_PSD K) (c d : ι →₀ ℂ) :
    conj (osr_form K d c) = osr_form K c d := by
  unfold osr_form Finsupp.sum
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, osr_herm hK]
  ring

theorem osr_form_self_nonneg {K : ι → ι → ℂ} (hK : osr_PSD K) (c : ι →₀ ℂ) :
    0 ≤ osr_form K c c :=
  osr_psd_finset hK c.support c

theorem osr_form_single (K : ι → ι → ℂ) (i j : ι) :
    osr_form K (Finsupp.single i 1) (Finsupp.single j 1) = K i j := by
  simp [osr_form, Finsupp.sum_single_index]

/-! ## The pre-Hilbert space and its completion -/

/-- A positive-semidefinite kernel, bundled. -/
structure osr_Kernel (ι : Type) where
  K : ι → ι → ℂ
  psd : osr_PSD K

/-- The space of finitely supported formal combinations (a type synonym of ι →₀ ℂ carrying the
seminorm of the kernel). -/
def osr_Pre (_P : osr_Kernel ι) : Type := ι →₀ ℂ

variable (P : osr_Kernel ι)

instance : AddCommGroup (osr_Pre P) := inferInstanceAs (AddCommGroup (ι →₀ ℂ))
instance : Module ℂ (osr_Pre P) := inferInstanceAs (Module ℂ (ι →₀ ℂ))

/-- The pre-inner-product core given by the kernel. -/
instance osr_core : PreInnerProductSpace.Core ℂ (osr_Pre P) where
  inner c d := osr_form P.K c d
  conj_inner_symm c d := osr_form_conj P.psd c d
  re_inner_nonneg c := by
    have := (Complex.nonneg_iff.mp (osr_form_self_nonneg P.psd c)).1
    simpa using this
  add_left c c' d := osr_form_add_left P.K c c' d
  smul_left c d r := osr_form_smul_left P.K c d r

instance : SeminormedAddCommGroup (osr_Pre P) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (osr_Pre P) := InnerProductSpace.ofCore _

theorem osr_inner_pre (c d : osr_Pre P) : ⟪c, d⟫_ℂ = osr_form P.K c d := rfl

/-- The identity (ι →₀ ℂ) → osr_Pre P, as a linear map (to cross the type synonym). -/
def osr_mk : (ι →₀ ℂ) →ₗ[ℂ] osr_Pre P := LinearMap.id

/-- Null vectors are orthogonal to everything (Cauchy–Schwarz). -/
theorem osr_null_form (c : osr_Pre P) (hc : (osr_form P.K c c).re = 0) (d : osr_Pre P) :
    osr_form P.K c d = 0 := by
  have hn : ‖c‖ = 0 := by
    have h := @norm_sq_eq_re_inner ℂ (osr_Pre P) _ _ _ c
    rw [osr_inner_pre] at h
    simp only [RCLike.re_to_complex] at h
    rw [hc] at h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  have h := norm_inner_le_norm (𝕜 := ℂ) c d
  rw [hn, zero_mul, osr_inner_pre] at h
  exact norm_le_zero_iff.mp h

/-- The reconstructed Hilbert space: the completion of the pre-Hilbert space (separation by the
null space is built into `UniformSpace.Completion`). -/
abbrev osr_H : Type := UniformSpace.Completion (osr_Pre P)

example : CompleteSpace (osr_H P) := inferInstance
example : NormedAddCommGroup (osr_H P) := inferInstance
example : InnerProductSpace ℂ (osr_H P) := inferInstance

/-- The image of c in the completion vanishes iff c is a null vector. -/
theorem osr_coe_eq_zero_iff (c : osr_Pre P) :
    ((c : osr_H P) = 0) ↔ (osr_form P.K c c).re = 0 := by
  rw [← norm_eq_zero (a := (c : osr_H P)), UniformSpace.Completion.norm_coe]
  have h := @norm_sq_eq_re_inner ℂ (osr_Pre P) _ _ _ c
  rw [osr_inner_pre] at h
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  constructor
  · intro h0; rw [h0]; ring
  · intro h0; exact pow_eq_zero_iff two_ne_zero |>.mp h0

/-- The vector of the point i: the class of δ_i. -/
def osr_vec (i : ι) : osr_H P :=
  (osr_mk P (Finsupp.single i (1 : ℂ)) : osr_Pre P)

theorem osr_inner_vec (i j : ι) : ⟪osr_vec P i, osr_vec P j⟫_ℂ = P.K i j := by
  rw [osr_vec, osr_vec, UniformSpace.Completion.inner_coe, osr_inner_pre]
  exact osr_form_single P.K i j

/-- The span of the vectors δ_i is dense in the completion. -/
theorem osr_dense : Dense ((Submodule.span ℂ (Set.range (osr_vec P))) : Set (osr_H P)) := by
  refine (UniformSpace.Completion.denseRange_coe (α := osr_Pre P)).mono ?_
  have key : ∀ x : ι →₀ ℂ, ((osr_mk P x : osr_Pre P) : osr_H P) ∈
      Submodule.span ℂ (Set.range (osr_vec P)) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero =>
      rw [map_zero, UniformSpace.Completion.coe_zero]; exact Submodule.zero_mem _
    | add f g hf hg =>
      rw [map_add, UniformSpace.Completion.coe_add]; exact Submodule.add_mem _ hf hg
    | single i a =>
      have e : (Finsupp.single i a : ι →₀ ℂ) = a • Finsupp.single i (1 : ℂ) := by simp
      rw [e, map_smul, UniformSpace.Completion.coe_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
  rintro _ ⟨c, rfl⟩
  exact key c

end Kernel

/-! ## The OS case: Z on positive-time test functions -/

section OS

open PP2Target PP2RP2

/-- 0 is (vacuously) positive-time. -/
theorem positiveTime_zero : PositiveTime 0 := fun _x hx => absurd rfl hx

/-- The OS kernel (f, g) ↦ Z(g − Θf) on positive-time test functions. -/
def osr_kernel (Z : TestFn → ℂ) (hZ : OSPositive Z) : osr_Kernel {f : TestFn // PositiveTime f} where
  K f g := Z (g.1 - reflect f.1)
  psd m x c := hZ m (fun a => (x a).1) c (fun a => (x a).2)

/-- The OS Hilbert space of an OS-positive functional. -/
abbrev OSHilbert (Z : TestFn → ℂ) (hZ : OSPositive Z) : Type := osr_H (osr_kernel Z hZ)

open Classical in
/-- ψ f = class of δ_f (the class of e^{iφ(f)}) for positive-time f; 0 otherwise. -/
def osr_psi (Z : TestFn → ℂ) (hZ : OSPositive Z) (f : TestFn) : OSHilbert Z hZ :=
  if h : PositiveTime f then osr_vec (osr_kernel Z hZ) ⟨f, h⟩ else 0

/-- The OS matrix elements: ⟪ψ f, ψ g⟫ = Z(g − Θf) for positive-time f, g. -/
theorem osr_psi_inner (Z : TestFn → ℂ) (hZ : OSPositive Z) {f g : TestFn}
    (hf : PositiveTime f) (hg : PositiveTime g) :
    ⟪osr_psi Z hZ f, osr_psi Z hZ g⟫_ℂ = Z (g - reflect f) := by
  rw [osr_psi, osr_psi, dite_eq_left_of_eq_true (eq_true hf), dite_eq_left_of_eq_true (eq_true hg), osr_inner_vec]
  rfl

/-- The span of ψ(positive-time test functions) is dense. -/
theorem osr_psi_dense (Z : TestFn → ℂ) (hZ : OSPositive Z) :
    Dense ((Submodule.span ℂ (osr_psi Z hZ '' {f | PositiveTime f})) : Set (OSHilbert Z hZ)) := by
  refine (osr_dense (osr_kernel Z hZ)).mono ?_
  apply Submodule.span_mono
  rintro _ ⟨⟨f, hf⟩, rfl⟩
  exact ⟨f, hf, by rw [osr_psi, dite_eq_left_of_eq_true (eq_true hf)]⟩

/-- The vacuum Ω = ψ 0 is a unit vector when Z 0 = 1. -/
theorem osr_vacuum_norm (Z : TestFn → ℂ) (hZ : OSPositive Z) (h0 : Z 0 = 1) :
    ‖osr_psi Z hZ 0‖ = 1 := by
  have h := @norm_sq_eq_re_inner ℂ (OSHilbert Z hZ) _ _ _ (osr_psi Z hZ 0)
  rw [osr_psi_inner Z hZ positiveTime_zero positiveTime_zero] at h
  simp only [map_zero, sub_zero, h0, RCLike.re_to_complex, Complex.one_re] at h
  have hn := norm_nonneg (osr_psi Z hZ 0)
  nlinarith [sq_nonneg (‖osr_psi Z hZ 0‖ - 1)]

theorem osr_reflect_reflect (f : TestFn) : reflect (reflect f) = f := by
  ext x
  rw [reflect_apply, reflect_apply]
  congr 1
  ext i; fin_cases i <;> simp

/-- Hermiticity of the OS kernel from the standard hypotheses Z(−h) = conj Z(h) and
Θ-invariance Z(Θh) = Z(h), for all test functions. -/
theorem osr_kernel_herm_of {Z : TestFn → ℂ} (hconj : ∀ h, Z (-h) = conj (Z h))
    (hΘ : ∀ h, Z (reflect h) = Z h) (f g : TestFn) :
    conj (Z (g - reflect f)) = Z (f - reflect g) := by
  rw [← hconj, neg_sub, ← hΘ, map_sub, osr_reflect_reflect]

end OS

end PP2OSRecon
