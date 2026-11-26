import LongTable.P_mwwgf2cx_iollxj
import LongTable.R_PP2FreeVar2B

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Region.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction (BFS route), node M5 (F1, F2),
session 1. The free Dirichlet field of a region B ⊆ box and the free Simon–Lieb exit weight of the
ball B = physBall x l (namespace `PP2Target`; ε = `spacing n`, regionOp/regionGreen of
PP2FreeVar2, bondJ/zeroExt/regionTwoPt/physBall/SmallBoundarySum of PP2SimonLieb).

FORMALIZED (no sorry, axioms: propext, Classical.choice, Quot.sound).
F1 (free region measure).
* `dirAction_zeroExt`: dirAction (zeroExt B ψ) = ε² · ψ ⬝ᵥ regionOp B *ᵥ ψ
  (helpers `rg_sum_zeroExt`, `rg_zeroExt_apply`, `rg_quad_zeroExt`).
* `rg_scaledOp` = ε² • regionOp, `rg_scaledOp_posDef`, `rg_scaledOp_inv` (= ε⁻² • regionGreen),
  `rg_qweight_zeroExt` (the λ = 0 weight is `gaussWeight rg_scaledOp`).
* `regionTwoPt_free`: m₀ ≠ 0 → regionTwoPt n k m₀ 0 B x y = ε⁻² · regionGreen B x y for x, y ∈ B
  (`gauss_ibp_cov` on ℝ^B with F = ψ_y).
* `rg_regionGreen_nonneg`: regionGreen ≥ 0 entrywise (`nonneg_of_stieltjes`).
F2 (exit weights).
* `exit_le` (supersolution comparison): m₀ ≠ 0, (dirOp m₀ h)(w) ≥ 0 for w ∈ B ⇒
  Σ_{u∈B} Σ_{v∉B} bondJ u v · ε⁻² regionGreen B y u · h v ≤ h y (no sign condition on h needed:
  regionOp h|_B ≥ ε⁻² Σ_{v∉B} bondJ(·, v) h v on B, then apply regionGreen ≥ 0).
* `rg_H c a b p` = cosh(c(p₁ − a)) + cosh(c(p₂ − b)) on ℤ², `rg_h` its restriction to the box,
  `rg_H_neighbours` (sum over the four neighbours = (2cosh c + 2) H), `rg_ext_h_le`,
  `rg_dirOp_h_nonneg`: 2cosh c − 2 ≤ ε²m₀² ⇒ dirOp h ≥ 0 at every box site.
* `rg_two_cosh_sub_two_le` (|t| ≤ 1 ⇒ 2cosh t − 2 ≤ 2t²), `rg_kappa m₀` = min(1, |m₀|)/2,
  `rg_mass_cond`: 2cosh(κε) − 2 ≤ ε²m₀² for every n.
* `rg_not_mem_physBall` (v ∉ ball ⇒ l < ε|Δ₁| or l < ε|Δ₂|), `rg_mem_physBall_self`.
* **`free_boundary_le`**: m₀ ≠ 0, 0 ≤ l ⇒ for all n, k, x,
  Σ_{u∈B} Σ_{v∉B} bondJ u v · ε⁻² regionGreen B x u ≤ 2/cosh(κ l), B = physBall n k x l,
  κ = min(1, |m₀|)/2 (h = rg_h with c = κε centred at x: h(x) = 2, h ≥ cosh(κl) off B).
* `rg_exit_weight_le_one` (h ≡ 2: exit weight ≤ 1 for every region), `rg_two_div_cosh_le`
  (2/cosh t ≤ 4e^{−t}).
* `rg_smallBoundarySum_free`: SmallBoundarySum m₀ 0 l (2/cosh(κ l)) (F1 + F2 in M6 form).

NOT formalized here: the rectangle equivalence {z // z ∈ physBall} ≃ Fin N₁ × Fin N₂ and the sine
diagonalisation of regionOp (F1, not needed for F2); the plan's sharper rate κ = 0.96·min(1, m₀)
(we prove κ = min(1, |m₀|)/2, which suffices: any explicit bound → 0 as l → ∞, uniformly);
anything at λ > 0 (I1, I2); F3, F4.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory Matrix Finset

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-! ## F1: the free region measure -/

theorem rg_sum_zeroExt (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) (f : DSite n k → ℝ) :
    ∑ a, zeroExt B ψ a * f a = ∑ a : {x // x ∈ B}, ψ a * f a := by
  rw [← Finset.sum_subset (Finset.subset_univ B) (fun a _ ha => by simp [zeroExt, ha]),
    ← Finset.sum_coe_sort B]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [zeroExt, a.2]

theorem rg_zeroExt_apply (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) (x : {x // x ∈ B}) :
    zeroExt B ψ x = ψ x := by
  simp [zeroExt, x.2]

theorem rg_quad_zeroExt (m₀ : ℝ) (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) :
    zeroExt B ψ ⬝ᵥ dirOp n k m₀ *ᵥ zeroExt B ψ = ψ ⬝ᵥ regionOp n k m₀ B *ᵥ ψ := by
  simp only [dotProduct, mulVec]
  rw [rg_sum_zeroExt]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp_rw [mul_comm (dirOp n k m₀ _ _)]
  rw [rg_sum_zeroExt]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [regionOp, mul_comm]

/-- **F1: the action of a zero-extended field** is ε² times the quadratic form of `regionOp`. -/
theorem dirAction_zeroExt (m₀ : ℝ) (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) :
    dirAction n k m₀ (zeroExt B ψ) = spacing n ^ 2 * (ψ ⬝ᵥ regionOp n k m₀ B *ᵥ ψ) := by
  rw [dirAction_eq_quad, rg_quad_zeroExt]

/-- The scaled region operator ε² • regionOp. -/
def rg_scaledOp (n k : ℕ) (m₀ : ℝ) (B : Finset (DSite n k)) :
    Matrix {x // x ∈ B} {x // x ∈ B} ℝ :=
  (spacing n ^ 2) • regionOp n k m₀ B

theorem rg_scaledOp_posDef {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) :
    (rg_scaledOp n k m₀ B).PosDef :=
  (fv2_regionOp_posDef hm B).smul (pow_pos (spacing_pos n) 2)

theorem rg_scaledOp_inv {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) :
    (rg_scaledOp n k m₀ B)⁻¹ = (spacing n ^ 2)⁻¹ • regionGreen n k m₀ B := by
  apply inv_eq_right_inv
  rw [rg_scaledOp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, fv2_regionOp_mul_regionGreen hm,
    mul_inv_cancel₀ (pow_ne_zero 2 (spacing_pos n).ne'), one_smul]

theorem rg_qweight_zeroExt (m₀ : ℝ) (B : Finset (DSite n k)) (ψ : {x // x ∈ B} → ℝ) :
    qweight n k m₀ 0 (zeroExt B ψ) = PP2GaussIBP.gaussWeight (rg_scaledOp n k m₀ B) ψ := by
  rw [qweight, dweight, PP2GaussIBP.gaussWeight, dirAction_zeroExt, rg_scaledOp, smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  simp

/-- **F1: the free region two-point function** is ε⁻² · regionGreen. -/
theorem regionTwoPt_free {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (x y : {z // z ∈ B}) :
    regionTwoPt n k m₀ 0 B x y = (spacing n ^ 2)⁻¹ * regionGreen n k m₀ B x y := by
  have hA := rg_scaledOp_posDef hm B
  have hfd : ∀ φ : {z // z ∈ B} → ℝ, fderiv ℝ (fun ψ : {z // z ∈ B} → ℝ => ψ y) φ =
      ContinuousLinearMap.proj y := fun φ => (hasFDerivAt_apply y φ).fderiv
  have hsum : ∀ φ : {z // z ∈ B} → ℝ, |φ y| ≤ 1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro φ
    have h1 : |φ y| ≤ ∑ i, |φ i| :=
      Finset.single_le_sum (f := fun i => |φ i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y)
    have h2 := Real.add_one_le_exp (∑ i, |φ i|)
    rw [one_mul, one_mul]; linarith
  have hF' : ∀ (z : {z // z ∈ B}) (φ : {z // z ∈ B} → ℝ),
      |fderiv ℝ (fun ψ : {z // z ∈ B} → ℝ => ψ y) φ (Pi.single z 1)| ≤
        1 * Real.exp (1 * ∑ i, |φ i|) := by
    intro z φ
    rw [hfd, ContinuousLinearMap.proj_apply]
    have h1 : |(Pi.single z (1 : ℝ) : {z // z ∈ B} → ℝ) y| ≤ 1 := by
      rw [Pi.single_apply]; split_ifs <;> norm_num
    have h2 : 1 ≤ Real.exp (1 * ∑ i, |φ i|) :=
      Real.one_le_exp (mul_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    linarith
  have key := PP2GaussIBP.gauss_ibp_cov hA (F := fun ψ : {z // z ∈ B} → ℝ => ψ y)
    (differentiable_apply y) 1 1 x hsum hF'
  simp only [hfd, ContinuousLinearMap.proj_apply] at key
  have hint : Integrable (fun φ : {z // z ∈ B} → ℝ =>
      PP2GaussIBP.gaussWeight (rg_scaledOp n k m₀ B) φ) := by
    simpa using PP2GaussIBP.integrable_expAbs_mul_gaussWeight hA 0
  have hpos : 0 < ∫ φ : {z // z ∈ B} → ℝ, PP2GaussIBP.gaussWeight (rg_scaledOp n k m₀ B) φ := by
    have := integral_exp_pos (μ := volume)
      (f := fun φ : {z // z ∈ B} → ℝ => -(φ ⬝ᵥ rg_scaledOp n k m₀ B *ᵥ φ) / 2) hint
    simpa [PP2GaussIBP.gaussWeight] using this
  rw [regionTwoPt]
  simp_rw [rg_zeroExt_apply, rg_qweight_zeroExt]
  rw [key, Finset.sum_eq_single y, rg_scaledOp_inv hm]
  · simp only [Pi.single_eq_same, one_mul, Matrix.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, div_self hpos.ne', mul_one]
  · intro z _ hz
    simp [Pi.single_eq_of_ne (Ne.symm hz)]
  · simp

/-- **F1: the region Green's function is entrywise nonnegative.** -/
theorem rg_regionGreen_nonneg {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (x y : {z // z ∈ B}) : 0 ≤ regionGreen n k m₀ B x y := by
  set A := regionOp n k m₀ B with hA
  have hsymm : Aᵀ = A := by
    rw [hA, regionOp, transpose_submatrix, dirOp_transpose]
  have hpd : ∀ v : {z // z ∈ B} → ℝ, v ≠ 0 → 0 < v ⬝ᵥ A *ᵥ v := fun v hv => by
    simpa using (fv2_regionOp_posDef hm B).dotProduct_mulVec_pos hv
  have hoff : ∀ a b : {z // z ∈ B}, a ≠ b → A a b ≤ 0 := fun a b hab =>
    dirOp_offDiag_nonpos m₀ (fun h => hab (Subtype.ext h))
  have hAu : A *ᵥ (regionGreen n k m₀ B *ᵥ Pi.single y 1) = Pi.single y 1 := by
    rw [mulVec_mulVec, hA, fv2_regionOp_mul_regionGreen hm, one_mulVec]
  have hd := nonneg_of_stieltjes A hsymm hpd hoff hAu
    (fun z => by rw [Pi.single_apply]; split_ifs <;> norm_num) x
  simpa [mulVec_single_one] using hd

/-! ## F2: supersolution comparison and the free exit weight -/

/-- **F2: supersolution comparison.** If (dirOp h)(w) ≥ 0 on B, then the free exit weight of
y ∈ B, weighted by h outside B, is at most h(y). -/
theorem exit_le {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k)) (h : DField n k)
    (hsup : ∀ w ∈ B, 0 ≤ (dirOp n k m₀ *ᵥ h) w) (y : {z // z ∈ B}) :
    ∑ u : {z // z ∈ B}, ∑ v ∈ Bᶜ,
        bondJ n k u v * ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y u) * h v ≤ h y := by
  set A := regionOp n k m₀ B with hA
  set G := regionGreen n k m₀ B with hG
  set hB : {z // z ∈ B} → ℝ := fun z => h z with hhB
  set f : {z // z ∈ B} → ℝ := fun u => ∑ v ∈ Bᶜ, (spacing n ^ 2)⁻¹ * bondJ n k u v * h v
    with hf
  have hε : spacing n ^ 2 ≠ 0 := pow_ne_zero 2 (spacing_pos n).ne'
  have hAf : ∀ u, f u ≤ (A *ᵥ hB) u := by
    intro u
    have hfull : (dirOp n k m₀ *ᵥ h) u =
        ∑ w ∈ B, dirOp n k m₀ u w * h w + ∑ w ∈ Bᶜ, dirOp n k m₀ u w * h w := by
      simp only [mulVec, dotProduct]; rw [Finset.sum_add_sum_compl]
    have hsub : (A *ᵥ hB) u = ∑ w ∈ B, dirOp n k m₀ u w * h w := by
      simp only [mulVec, dotProduct, hA, regionOp, submatrix_apply, hhB]
      exact Finset.sum_coe_sort B (fun w => dirOp n k m₀ u w * h w)
    have hout : ∑ w ∈ Bᶜ, dirOp n k m₀ u w * h w = -f u := by
      simp only [hf, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w hw => ?_
      have huw : (u : DSite n k) ≠ w := by
        rintro h'; rw [← h'] at hw; exact (Finset.mem_compl.mp hw) u.2
      rw [bondJ, dirOp_offDiag_mass m₀ huw, mul_neg, ← mul_assoc, inv_mul_cancel₀ hε, one_mul,
        neg_mul, neg_neg]
    have := hsup u u.2
    linarith
  have hGA : G * A = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (fv2_regionOp_posDef hm B).isUnit)
  have hy : h y = ∑ u, G y u * (A *ᵥ hB) u := by
    have : G *ᵥ (A *ᵥ hB) = hB := by rw [mulVec_mulVec, hGA, one_mulVec]
    exact (congrFun this y).symm
  rw [hy]
  calc _ = ∑ u, G y u * f u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [hf, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ ≤ _ := Finset.sum_le_sum fun u _ =>
        mul_le_mul_of_nonneg_left (hAf u) (rg_regionGreen_nonneg hm B y u)

/-- The lattice test function H(p) = cosh(c(p₁ − a)) + cosh(c(p₂ − b)) on ℤ². -/
def rg_H (c a b : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.cosh (c * ((p.1 : ℝ) - a)) + Real.cosh (c * ((p.2 : ℝ) - b))

/-- Its restriction to the box. -/
def rg_h (n k : ℕ) (c a b : ℝ) : DField n k := fun w => rg_H c a b (site w)

theorem rg_H_pos (c a b : ℝ) (p : ℤ × ℤ) : 0 < rg_H c a b p := by
  unfold rg_H; have := Real.cosh_pos (c * ((p.1 : ℝ) - a))
  have := Real.cosh_pos (c * ((p.2 : ℝ) - b)); linarith

theorem rg_ext_h_le (c a b : ℝ) (q : ℤ × ℤ) : ext (rg_h n k c a b) q ≤ rg_H c a b q := by
  unfold ext
  split_ifs with hq
  · apply le_of_eq
    show rg_H c a b (((q.1.toNat : ℕ) : ℤ), ((q.2.toNat : ℕ) : ℤ)) = rg_H c a b q
    rw [Int.toNat_of_nonneg hq.1, Int.toNat_of_nonneg hq.2.2.1]
  · exact (rg_H_pos c a b q).le

theorem rg_H_neighbours (c a b : ℝ) (s : ℤ × ℤ) :
    rg_H c a b (s.1 - 1, s.2) + rg_H c a b (s.1 + 1, s.2) + rg_H c a b (s.1, s.2 - 1)
      + rg_H c a b (s.1, s.2 + 1) = (2 * Real.cosh c + 2) * rg_H c a b s := by
  simp only [rg_H]
  push_cast
  rw [show c * ((s.1 : ℝ) - 1 - a) = c * ((s.1 : ℝ) - a) - c by ring,
    show c * ((s.1 : ℝ) + 1 - a) = c * ((s.1 : ℝ) - a) + c by ring,
    show c * ((s.2 : ℝ) - 1 - b) = c * ((s.2 : ℝ) - b) - c by ring,
    show c * ((s.2 : ℝ) + 1 - b) = c * ((s.2 : ℝ) - b) + c by ring,
    Real.cosh_sub, Real.cosh_add, Real.cosh_sub, Real.cosh_add]
  ring

/-- **The cosh supersolution:** if 2cosh c − 2 ≤ ε² m₀², then dirOp h ≥ 0 at every box site
(neighbours outside the box only help, since H > 0). -/
theorem rg_dirOp_h_nonneg {m₀ c : ℝ} (a b : ℝ)
    (hc : 2 * Real.cosh c - 2 ≤ spacing n ^ 2 * m₀ ^ 2) (w : DSite n k) :
    0 ≤ (dirOp n k m₀ *ᵥ rg_h n k c a b) w := by
  rw [dirOp_mulVec_apply]
  have e1 := rg_ext_h_le (n := n) (k := k) c a b ((site w).1 - 1, (site w).2)
  have e2 := rg_ext_h_le (n := n) (k := k) c a b ((site w).1 + 1, (site w).2)
  have e3 := rg_ext_h_le (n := n) (k := k) c a b ((site w).1, (site w).2 - 1)
  have e4 := rg_ext_h_le (n := n) (k := k) c a b ((site w).1, (site w).2 + 1)
  have hs := rg_H_neighbours c a b (site w)
  have hw : rg_h n k c a b w = rg_H c a b (site w) := rfl
  have hH := rg_H_pos c a b (site w)
  have hP : 0 < (spacing n ^ 2)⁻¹ := inv_pos.mpr (pow_pos (spacing_pos n) 2)
  have hPm : (spacing n ^ 2)⁻¹ * (2 * Real.cosh c - 2) ≤ m₀ ^ 2 := by
    calc (spacing n ^ 2)⁻¹ * (2 * Real.cosh c - 2) ≤ (spacing n ^ 2)⁻¹ * (spacing n ^ 2 * m₀ ^ 2) :=
          mul_le_mul_of_nonneg_left hc hP.le
      _ = m₀ ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (spacing_pos n).ne'), one_mul]
  rw [hw]
  have hin : (2 - 2 * Real.cosh c) * rg_H c a b (site w) ≤
      (2 * rg_H c a b (site w) - ext (rg_h n k c a b) ((site w).1 - 1, (site w).2)
          - ext (rg_h n k c a b) ((site w).1 + 1, (site w).2))
        + (2 * rg_H c a b (site w) - ext (rg_h n k c a b) ((site w).1, (site w).2 - 1)
          - ext (rg_h n k c a b) ((site w).1, (site w).2 + 1)) := by
    linarith
  calc (0 : ℝ) ≤ (m₀ ^ 2 - (spacing n ^ 2)⁻¹ * (2 * Real.cosh c - 2)) * rg_H c a b (site w) :=
        mul_nonneg (by linarith) hH.le
    _ = (spacing n ^ 2)⁻¹ * ((2 - 2 * Real.cosh c) * rg_H c a b (site w))
          + m₀ ^ 2 * rg_H c a b (site w) := by ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hin hP.le) _

/-- 2cosh t − 2 ≤ 2t² for |t| ≤ 1. -/
theorem rg_two_cosh_sub_two_le {t : ℝ} (ht : |t| ≤ 1) : 2 * Real.cosh t - 2 ≤ 2 * t ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq t
  have ht2 : t ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hs0 : 0 ≤ t ^ 2 / 2 := by positivity
  have hs : |t ^ 2 / 2| ≤ 1 := by rw [abs_of_nonneg hs0]; linarith
  have h2 := Real.abs_exp_sub_one_sub_id_le hs
  have h3 := (abs_le.mp h2).2
  have h4 : (t ^ 2 / 2) ^ 2 ≤ t ^ 2 / 2 := by nlinarith
  linarith

/-- The decay rate κ(m₀) = min(1, |m₀|)/2. -/
def rg_kappa (m₀ : ℝ) : ℝ := min 1 |m₀| / 2

theorem rg_kappa_pos {m₀ : ℝ} (hm : m₀ ≠ 0) : 0 < rg_kappa m₀ := by
  unfold rg_kappa; have := abs_pos.mpr hm; positivity

theorem rg_mass_cond (m₀ : ℝ) (n : ℕ) :
    2 * Real.cosh (rg_kappa m₀ * spacing n) - 2 ≤ spacing n ^ 2 * m₀ ^ 2 := by
  have hε := spacing_pos n
  have hε1 := spacing_le_one n
  have hk0 : 0 ≤ rg_kappa m₀ := by unfold rg_kappa; positivity
  have hk1 : rg_kappa m₀ ≤ 1 / 2 := by unfold rg_kappa; linarith [min_le_left 1 |m₀|]
  have hk2 : rg_kappa m₀ ≤ |m₀| / 2 := by unfold rg_kappa; linarith [min_le_right 1 |m₀|]
  have ht : |rg_kappa m₀ * spacing n| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have h := rg_two_cosh_sub_two_le ht
  have hk3 : rg_kappa m₀ ^ 2 ≤ m₀ ^ 2 / 4 := by
    have : rg_kappa m₀ ^ 2 ≤ (|m₀| / 2) ^ 2 := pow_le_pow_left₀ hk0 hk2 2
    rw [div_pow, sq_abs] at this; linarith
  have : 2 * (rg_kappa m₀ * spacing n) ^ 2 ≤ spacing n ^ 2 * m₀ ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg (spacing n)]
  linarith

theorem rg_mem_physBall_self {l : ℝ} (hl : 0 ≤ l) (x : DSite n k) : x ∈ physBall n k x l :=
  mem_physBall.mpr (by rw [supDist_self]; exact hl)

/-- Sites outside the ball have a lattice coordinate offset > l/ε. -/
theorem rg_not_mem_physBall {l : ℝ} {x v : DSite n k} (hv : v ∉ physBall n k x l) :
    l < spacing n * |((v.1 : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ)| ∨
      l < spacing n * |((v.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)| := by
  rw [mem_physBall, not_le] at hv
  unfold supDist at hv
  rw [dpos_zero, dpos_zero, dpos_one, dpos_one] at hv
  have e1 : spacing n * ((x.1 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((v.1 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((x.1 : ℕ) : ℝ) - ((v.1 : ℕ) : ℝ)) := by ring
  have e2 : spacing n * ((x.2 : ℕ) : ℝ) - boxL k / 2 - (spacing n * ((v.2 : ℕ) : ℝ) - boxL k / 2)
      = spacing n * (((x.2 : ℕ) : ℝ) - ((v.2 : ℕ) : ℝ)) := by ring
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos (spacing_pos n), abs_sub_comm ((x.1 : ℕ) : ℝ),
    abs_sub_comm ((x.2 : ℕ) : ℝ)] at hv
  exact lt_max_iff.mp hv

/-- **F2: the free exit weight of the ball** B = physBall x l is at most 2/cosh(κ l),
κ = min(1, |m₀|)/2, uniformly in the level n, the volume k and the centre x. -/
theorem free_boundary_le {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) (n k : ℕ) (x : DSite n k) :
    ∑ u : {z // z ∈ physBall n k x l}, ∑ v ∈ (physBall n k x l)ᶜ,
        bondJ n k u v * ((spacing n ^ 2)⁻¹ *
          regionGreen n k m₀ (physBall n k x l) ⟨x, rg_mem_physBall_self hl x⟩ u)
      ≤ 2 / Real.cosh (rg_kappa m₀ * l) := by
  set B := physBall n k x l with hBdef
  set c := rg_kappa m₀ * spacing n with hcdef
  set h : DField n k := rg_h n k c ((x.1 : ℕ) : ℝ) ((x.2 : ℕ) : ℝ) with hhdef
  have hex := exit_le hm B h (fun w _ => rg_dirOp_h_nonneg _ _ (rg_mass_cond m₀ n) w)
    ⟨x, rg_mem_physBall_self hl x⟩
  have hx2 : h x = 2 := by
    simp only [hhdef, rg_h, rg_H, site, Int.cast_natCast, sub_self, mul_zero, Real.cosh_zero]
    norm_num
  have hκ := rg_kappa_pos hm
  have hC : 0 < Real.cosh (rg_kappa m₀ * l) := Real.cosh_pos _
  have hv : ∀ v ∈ Bᶜ, Real.cosh (rg_kappa m₀ * l) ≤ h v := by
    intro v hvB
    have hvn : v ∉ B := Finset.mem_compl.mp hvB
    have hval : h v = Real.cosh (c * (((v.1 : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ)))
        + Real.cosh (c * (((v.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ))) := by
      simp only [hhdef, rg_h, rg_H, site, Int.cast_natCast]
    have hl' : |rg_kappa m₀ * l| = rg_kappa m₀ * l := abs_of_nonneg (by positivity)
    have hc0 : 0 ≤ c := by rw [hcdef]; exact mul_nonneg hκ.le (spacing_pos n).le
    rw [hval]
    rcases rg_not_mem_physBall hvn with h1 | h1
    · have : Real.cosh (rg_kappa m₀ * l) ≤
          Real.cosh (c * (((v.1 : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ))) := by
        rw [Real.cosh_le_cosh, hl', abs_mul, abs_of_nonneg hc0, hcdef, mul_assoc]
        exact mul_le_mul_of_nonneg_left h1.le hκ.le
      linarith [Real.cosh_pos (c * (((v.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)))]
    · have : Real.cosh (rg_kappa m₀ * l) ≤
          Real.cosh (c * (((v.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ))) := by
        rw [Real.cosh_le_cosh, hl', abs_mul, abs_of_nonneg hc0, hcdef, mul_assoc]
        exact mul_le_mul_of_nonneg_left h1.le hκ.le
      linarith [Real.cosh_pos (c * (((v.1 : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ)))]
  rw [le_div_iff₀ hC]
  calc _ = ∑ u : {z // z ∈ B}, ∑ v ∈ Bᶜ, bondJ n k u v * ((spacing n ^ 2)⁻¹ *
          regionGreen n k m₀ B ⟨x, rg_mem_physBall_self hl x⟩ u) * Real.cosh (rg_kappa m₀ * l) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v hvB => ?_
        have huv : (u : DSite n k) ≠ v := by
          rintro h'; rw [← h'] at hvB; exact (Finset.mem_compl.mp hvB) u.2
        refine mul_le_mul_of_nonneg_left (hv v hvB) (mul_nonneg (bondJ_nonneg huv)
          (mul_nonneg (inv_nonneg.mpr (by positivity)) (rg_regionGreen_nonneg hm B _ u)))
    _ ≤ h x := hex
    _ = 2 := hx2

/-- **F2, h ≡ 2:** the free exit weight of any region is at most 1. -/
theorem rg_exit_weight_le_one {m₀ : ℝ} (hm : m₀ ≠ 0) (B : Finset (DSite n k))
    (y : {z // z ∈ B}) :
    ∑ u : {z // z ∈ B}, ∑ v ∈ Bᶜ,
        bondJ n k u v * ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y u) ≤ 1 := by
  have hc : 2 * Real.cosh 0 - 2 ≤ spacing n ^ 2 * m₀ ^ 2 := by
    rw [Real.cosh_zero]; norm_num; positivity
  have hex := exit_le hm B (rg_h n k 0 0 0) (fun w _ => rg_dirOp_h_nonneg 0 0 hc w) y
  have h2 : ∀ w : DSite n k, rg_h n k 0 0 0 w = 2 := fun w => by
    simp only [rg_h, rg_H, zero_mul, Real.cosh_zero]; norm_num
  simp only [h2] at hex
  have : ∑ u : {z // z ∈ B}, ∑ v ∈ Bᶜ, bondJ n k u v *
      ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y u) * 2 = 2 * ∑ u : {z // z ∈ B}, ∑ v ∈ Bᶜ,
        bondJ n k u v * ((spacing n ^ 2)⁻¹ * regionGreen n k m₀ B y u) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_; ring
  linarith

/-- 2/cosh t ≤ 4 e^{−t}: the bound of `free_boundary_le` decays exponentially in l. -/
theorem rg_two_div_cosh_le (t : ℝ) : 2 / Real.cosh t ≤ 4 * Real.exp (-t) := by
  have hC := Real.cosh_pos t
  have he : Real.exp t / 2 ≤ Real.cosh t := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-t)]
  rw [div_le_iff₀ hC, Real.exp_neg]
  have hpos := Real.exp_pos t
  calc (2 : ℝ) = 4 * (Real.exp t)⁻¹ * (Real.exp t / 2) := by field_simp; norm_num
    _ ≤ 4 * (Real.exp t)⁻¹ * Real.cosh t :=
        mul_le_mul_of_nonneg_left he (by positivity)

/-- **F1 + F2 in the M6 form:** the free (λ = 0) model satisfies `SmallBoundarySum` with
γ = 2/cosh(κ l). -/
theorem rg_smallBoundarySum_free {m₀ : ℝ} (hm : m₀ ≠ 0) {l : ℝ} (hl : 0 ≤ l) :
    SmallBoundarySum m₀ 0 l (2 / Real.cosh (rg_kappa m₀ * l)) := by
  intro n k x
  have hx := rg_mem_physBall_self (n := n) (k := k) hl x
  refine le_of_eq_of_le ?_ (free_boundary_le hm hl n k x)
  rw [← Finset.sum_coe_sort (physBall n k x l)]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  exact congrArg (bondJ n k u v * ·) (regionTwoPt_free hm _ ⟨x, hx⟩ u)

end PP2Target
