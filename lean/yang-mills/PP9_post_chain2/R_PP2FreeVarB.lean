import LongTable.R_PP2FreeVarA

/-!
Part B of PP2FreeVar (split for the 24,000-character limit; same content as congress-lean lean/yang-mills/PP7_parallel_round1/PP2FreeVar.lean)

FORMALIZED in this part (no sorry, axioms: propext, Classical.choice, Quot.sound).
* `sineVec_centre_sq`: for N = 2M + 1, e_j(M)² = 1/(M+1) if j is even (mode j+1 odd), else 0
  (verified: 2/(N+1) = 1/(M+1)).
* `specVar_centre` (**goal 2, identity**): specVar (2M+1) μ M M =
  Σ_{r₁,r₂ ≤ M} (M+1)⁻² / w(θ_{r₁}, θ_{r₂}); since (M+1)⁻² = (h/π)², this is the midpoint rule
  with M+1 cells of width h = 2π/(N+1) on [0, π] for (1/π²)∫∫_{[0,π]²} 1/w.
* `integral_le_midpoint_sum`: f ≥ 0 antitone on [0, π] → ∫_{h/2}^{π} f ≤ h Σ_{r≤M} f(θ_r).
* `inv_symb_anti₁/₂`: 1/w is antitone in each θ_i on [0, π] (μ > 0).
* `specVar_centre_ge`: (1/π²) ∫∫_{[h/2, π]²} 1/w ≤ specVar (2M+1) μ M M (μ > 0).
* `freeVar_eq_quarter`: freeVar = (1/π²) ∫_0^π ∫_0^π 1/w (evenness, m₀ ≠ 0).
* `freeVar_sub_specVar_centre_le` (**goal 2, strip bound**): m₀ ≠ 0 →
  freeVar − specVar (2M+1) (m₀²ε²) M M ≤ (1/π²)(∫_0^{h/2}∫_0^π 1/w + ∫_0^π∫_0^{h/2} 1/w).

NOT formalized here: the explicit estimate of the strip integrals by C(1 + log₊(1/(m₀ε(M+1))))
(needs Jordan sin x ≥ 2x/π and ∫ dθ/(a + bθ²) bounds), the θ₁ ↔ θ₂ swap making the two strips
equal; any link from `specVar (2M+1)` to `dirGreen` (the repo's box has even side 2^(n+k), so the
odd sub-box centred at x is not itself a `DSite` box); domain monotonicity (goal 3:
G_{sub-box} ≤ G_box on the sub-box); hence no bound b(x) ≤ C(1 + log₊(1/(m₀ r))) yet.

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open Matrix Real Finset

noncomputable section

namespace PP2Target

variable {n k : ℕ}

/-- **The centre of an odd box.** For N = 2M + 1 and the centre site i = M:
e_j(M)² = 1/(M+1) if j is even (mode number j + 1 odd), and 0 if j is odd. -/
theorem sineVec_centre_sq (M j : ℕ) (hM : M < 2 * M + 1) :
    sineVec (2 * M + 1) j ⟨M, hM⟩ ^ 2 = if Even j then 1 / ((M : ℝ) + 1) else 0 := by
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  simp only [sineVec, sineFn]
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have harg : π * ((M : ℝ) + 1) * ((j : ℝ) + 1) / (((2 * M + 1 : ℕ) : ℝ) + 1) =
      π / 2 + (j : ℝ) * (π / 2) := by
    push_cast; field_simp; ring
  rw [harg]
  have h2 : (2 : ℝ) / (((2 * M + 1 : ℕ) : ℝ) + 1) = 1 / ((M : ℝ) + 1) := by
    push_cast; field_simp; ring
  rw [h2]
  split_ifs with hj
  · obtain ⟨r, rfl⟩ := hj
    rw [show ((r + r : ℕ) : ℝ) * (π / 2) = (r : ℕ) * π by push_cast; ring,
      Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]
    have h1 : ((-1 : ℝ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h1, mul_one]
  · obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hj
    rw [show π / 2 + ((2 * r + 1 : ℕ) : ℝ) * (π / 2) = ((r + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi]
    ring

/-- Even-index extraction: Σ_{j < 2M+1} [j even] f(j) = Σ_{r < M+1} f(2r). -/
theorem sum_range_even_odd_split {β : Type*} [AddCommMonoid β] (f : ℕ → β) (M : ℕ) :
    ∑ j ∈ range (2 * M + 1), (if Even j then f j else 0) = ∑ r ∈ range (M + 1), f (2 * r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (fun r => f (2 * r)) (M + 1)]
    have h1 : ¬ Even (2 * M + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one M)
    have h2 : Even (2 * M + 1 + 1) := ⟨M + 1, by ring⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), add_zero, show 2 * M + 1 + 1 = 2 * (M + 1) by ring]

theorem sum_fin_fin {β : Type*} [AddCommMonoid β] (N : ℕ) (g : ℕ → ℕ → β) :
    ∑ x : Fin N, ∑ y : Fin N, g x y = ∑ x ∈ range N, ∑ y ∈ range N, g x y := by
  rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin N, g x y)]
  exact Finset.sum_congr rfl fun x _ => Fin.sum_univ_eq_sum_range (g x) N

/-- The midpoint nodes θ_r = π(2r+1)/(2(M+1)), r = 0..M, of the M + 1 cells of width π/(M+1)
tiling [0, π]. -/
def midNode (M r : ℕ) : ℝ := π * (2 * (r : ℝ) + 1) / (2 * ((M : ℝ) + 1))

theorem sineEig_even_odd_box (M r : ℕ) :
    sineEig (2 * M + 1) (2 * r) = 4 * sin (midNode M r / 2) ^ 2 := by
  simp only [sineEig, midNode]
  congr 3
  push_cast
  field_simp
  ring

/-- **Centre-site identity.** At the centre of an odd box N = 2M + 1, the spectral site variance
is the midpoint Riemann sum of the `freeVar` integrand over the M + 1 cells of [0, π] in each
direction (weights (1/(M+1))² = (h/π)², h = π/(M+1); by evenness, (1/π²)∫∫_{[0,π]²} = freeVar
up to normalisation):
specVar (2M+1) μ M M = Σ_{r₁, r₂ ≤ M} (M+1)⁻² / w(θ_{r₁}, θ_{r₂}). -/
theorem specVar_centre (M : ℕ) (μ : ℝ) (hM : M < 2 * M + 1) :
    specVar (2 * M + 1) μ ⟨M, hM⟩ ⟨M, hM⟩ =
      ∑ r₁ ∈ range (M + 1), ∑ r₂ ∈ range (M + 1),
        (1 / ((M : ℝ) + 1)) ^ 2 / symb μ (midNode M r₁) (midNode M r₂) := by
  unfold specVar
  simp only [sineVec_centre_sq]
  have hpt : ∀ j₁ j₂ : ℕ,
      (if Even j₁ then 1 / ((M : ℝ) + 1) else 0) * (if Even j₂ then 1 / ((M : ℝ) + 1) else 0) /
          (μ + sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂) =
        if Even j₁ then (if Even j₂ then
          (1 / ((M : ℝ) + 1)) ^ 2 / (μ + sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂) else 0)
          else 0 := by
    intro j₁ j₂
    split_ifs <;> ring
  simp only [hpt]
  set F : ℕ → ℕ → ℝ := fun j₁ j₂ =>
    (1 / ((M : ℝ) + 1)) ^ 2 / (μ + sineEig (2 * M + 1) j₁ + sineEig (2 * M + 1) j₂) with hF
  refine (sum_fin_fin (2 * M + 1)
    (fun j₁ j₂ => if Even j₁ then (if Even j₂ then F j₁ j₂ else 0) else 0)).trans ?_
  have hin : ∀ j₁ : ℕ, ∑ j₂ ∈ range (2 * M + 1),
      (if Even j₁ then (if Even j₂ then F j₁ j₂ else 0) else 0) =
        if Even j₁ then ∑ j₂ ∈ range (2 * M + 1), (if Even j₂ then F j₁ j₂ else 0) else 0 := by
    intro j₁; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j₁ _ => hin j₁, sum_range_even_odd_split]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  rw [sum_range_even_odd_split]
  refine Finset.sum_congr rfl fun r₂ _ => ?_
  simp only [hF, sineEig_even_odd_box, symb]

/-! ## Midpoint sums of antitone functions -/

theorem midNode_eq (M r : ℕ) :
    midNode M r = π / ((M : ℝ) + 1) * r + π / ((M : ℝ) + 1) / 2 := by
  unfold midNode; field_simp

theorem midNode_nonneg (M r : ℕ) : 0 ≤ midNode M r := by unfold midNode; positivity

theorem midNode_le_pi (M r : ℕ) (hr : r ≤ M) : midNode M r ≤ π := by
  unfold midNode
  have hr' : (r : ℝ) ≤ M := by exact_mod_cast hr
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

/-- **Midpoint sum of an antitone function dominates the integral beyond the first half-cell**:
for f ≥ 0 antitone on [0, π], with h = π/(M+1),
∫_{h/2}^{π} f ≤ h Σ_{r ≤ M} f(θ_r)   (θ_r = (r + ½)h). -/
theorem integral_le_midpoint_sum {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc 0 π))
    (hf0 : ∀ t ∈ Set.Icc 0 π, 0 ≤ f t) (M : ℕ) :
    ∫ t in (midNode M 0)..π, f t ≤
      π / ((M : ℝ) + 1) * ∑ r ∈ range (M + 1), f (midNode M r) := by
  set h := π / ((M : ℝ) + 1) with hh
  have hpos : 0 < h := by positivity
  have hint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ π → IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab hb
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf.mono (Set.Icc_subset_Icc ha hb)
  have hstep : ∀ r, midNode M (r + 1) = midNode M r + h := by
    intro r; rw [midNode_eq, midNode_eq]; push_cast; ring
  have hmono : ∀ r, midNode M r ≤ midNode M (r + 1) := fun r => by rw [hstep]; linarith
  have hM : midNode M M ≤ π := midNode_le_pi M M le_rfl
  have hMpi : π - midNode M M = h / 2 := by
    rw [midNode_eq, hh]; field_simp; ring
  have hcell : ∀ r < M, ∫ t in (midNode M r)..(midNode M (r + 1)), f t ≤ h * f (midNode M r) := by
    intro r hr
    have h1 : midNode M (r + 1) ≤ π := midNode_le_pi M (r + 1) hr
    calc ∫ t in (midNode M r)..(midNode M (r + 1)), f t
        ≤ ∫ t in (midNode M r)..(midNode M (r + 1)), f (midNode M r) := by
          apply intervalIntegral.integral_mono_on (hmono r)
            (hint _ _ (midNode_nonneg M r) (hmono r) h1) intervalIntegrable_const
          intro t ht
          exact hf ⟨midNode_nonneg M r, by linarith [hmono r]⟩
            ⟨by linarith [ht.1, midNode_nonneg M r], by linarith [ht.2]⟩ ht.1
      _ = h * f (midNode M r) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hstep]; ring
  have hlast : ∫ t in (midNode M M)..π, f t ≤ h * f (midNode M M) := by
    have h0 : 0 ≤ f (midNode M M) := hf0 _ ⟨midNode_nonneg M M, hM⟩
    calc ∫ t in (midNode M M)..π, f t ≤ ∫ t in (midNode M M)..π, f (midNode M M) := by
          apply intervalIntegral.integral_mono_on hM
            (hint _ _ (midNode_nonneg M M) hM le_rfl) intervalIntegrable_const
          intro t ht
          exact hf ⟨midNode_nonneg M M, hM⟩ ⟨by linarith [ht.1, midNode_nonneg M M], ht.2⟩ ht.1
      _ = h / 2 * f (midNode M M) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hMpi]
      _ ≤ h * f (midNode M M) := by nlinarith
  have hsum : ∑ r ∈ range M, ∫ t in (midNode M r)..(midNode M (r + 1)), f t =
      ∫ t in (midNode M 0)..(midNode M M), f t := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro r hr
    exact hint _ _ (midNode_nonneg M r) (hmono r) (midNode_le_pi M (r + 1) hr)
  have hmono0 : midNode M 0 ≤ midNode M M := by
    rw [midNode_eq, midNode_eq]; have : (0 : ℝ) ≤ M := by positivity
    nlinarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint _ _ (midNode_nonneg M 0) hmono0 hM) (hint _ _ (midNode_nonneg M M) hM le_rfl),
    ← hsum, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun r hr => hcell r (Finset.mem_range.mp hr)) hlast

theorem sin_sq_half_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    sin (a / 2) ^ 2 ≤ sin (b / 2) ^ 2 := by
  have h0 : 0 ≤ sin (a / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have h1 : sin (a / 2) ≤ sin (b / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  exact pow_le_pow_left₀ h0 h1 2

theorem symb_pos {μ : ℝ} (hμ : 0 < μ) (θ₁ θ₂ : ℝ) : 0 < symb μ θ₁ θ₂ := by
  unfold symb; positivity

theorem inv_symb_anti₁ {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    AntitoneOn (fun θ => 1 / symb μ θ t) (Set.Icc 0 π) := by
  intro a ha b hb hab
  apply one_div_le_one_div_of_le (symb_pos hμ _ _)
  unfold symb
  linarith [sin_sq_half_mono ha.1 hab hb.2]

theorem inv_symb_anti₂ {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    AntitoneOn (fun θ => 1 / symb μ t θ) (Set.Icc 0 π) := by
  intro a ha b hb hab
  apply one_div_le_one_div_of_le (symb_pos hμ _ _)
  unfold symb
  linarith [sin_sq_half_mono ha.1 hab hb.2]

theorem continuous_inv_symb {μ : ℝ} (hμ : 0 < μ) :
    Continuous (fun q : ℝ × ℝ => 1 / symb μ q.1 q.2) :=
  continuous_const.div (by unfold symb; fun_prop) (fun q => (symb_pos hμ _ _).ne')

/-- **Lower bound at the centre of an odd box.** With h = π/(M+1) and w the symbol at lattice
mass² μ > 0, the centre-site spectral variance dominates the `freeVar`-type integral over the
square [h/2, π]²: (1/π²) ∫∫_{[h/2, π]²} 1/w ≤ specVar (2M+1) μ M M. Together with
freeVar = (1/π²)∫∫_{[0,π]²} 1/w (`freeVar_eq_quarter`), this leaves
freeVar − c_D(centre) ≤ (2/π²) ∫_0^{h/2} ∫_0^π 1/w, the boundary-strip term. -/
theorem specVar_centre_ge (M : ℕ) {μ : ℝ} (hμ : 0 < μ) (hM : M < 2 * M + 1) :
    1 / π ^ 2 * ∫ θ₁ in (midNode M 0)..π, ∫ θ₂ in (midNode M 0)..π, 1 / symb μ θ₁ θ₂ ≤
      specVar (2 * M + 1) μ ⟨M, hM⟩ ⟨M, hM⟩ := by
  have hpi := Real.pi_pos
  set h := π / ((M : ℝ) + 1) with hh
  have h0 : midNode M 0 ≤ π := midNode_le_pi M 0 (Nat.zero_le _)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun θ₁ => ∫ θ₂ in (midNode M 0)..π, 1 / symb μ θ₁ θ₂ :=
    ⟨_, rfl⟩
  have hcont₂ : ∀ θ₁, Continuous fun θ₂ => 1 / symb μ θ₁ θ₂ := fun θ₁ =>
    continuous_const.div (by unfold symb; fun_prop) (fun _ => (symb_pos hμ _ _).ne')
  have hganti : AntitoneOn g (Set.Icc 0 π) := by
    intro a ha b hb hab
    rw [hg]
    apply intervalIntegral.integral_mono_on h0 ((hcont₂ b).intervalIntegrable _ _)
      ((hcont₂ a).intervalIntegrable _ _)
    intro t _
    exact inv_symb_anti₁ hμ t ha hb hab
  have hg0 : ∀ t ∈ Set.Icc 0 π, 0 ≤ g t := by
    intro t _
    rw [hg]
    exact intervalIntegral.integral_nonneg h0 fun u _ => (one_div_pos.mpr (symb_pos hμ _ _)).le
  have step1 := integral_le_midpoint_sum hganti hg0 M
  have step2 : ∀ r₁ ∈ range (M + 1),
      g (midNode M r₁) ≤ h * ∑ r₂ ∈ range (M + 1), 1 / symb μ (midNode M r₁) (midNode M r₂) :=
    by
      intro r₁ _
      rw [hg]
      exact integral_le_midpoint_sum (inv_symb_anti₂ hμ _)
        (fun t _ => (one_div_pos.mpr (symb_pos hμ _ _)).le) M
  rw [specVar_centre]
  have hc : (1 / ((M : ℝ) + 1)) ^ 2 = 1 / π ^ 2 * (h * h) := by
    rw [hh]; field_simp
  have hsum : ∑ r₁ ∈ range (M + 1), ∑ r₂ ∈ range (M + 1),
      (1 / ((M : ℝ) + 1)) ^ 2 / symb μ (midNode M r₁) (midNode M r₂) =
      1 / π ^ 2 * (h * ∑ r₁ ∈ range (M + 1),
        h * ∑ r₂ ∈ range (M + 1), 1 / symb μ (midNode M r₁) (midNode M r₂)) := by
    rw [hc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r₁ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r₂ _ => ?_
    ring
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← hg]
  calc ∫ θ₁ in (midNode M 0)..π, g θ₁ ≤ h * ∑ r₁ ∈ range (M + 1), g (midNode M r₁) := step1
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum step2) (by positivity)

/-! ## `freeVar` as an integral over [0, π]² and the boundary-strip bound -/

theorem integral_even_pi {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t)
    (hint : IntervalIntegrable f MeasureTheory.volume (-π) π) :
    ∫ t in (-π)..π, f t = 2 * ∫ t in (0 : ℝ)..π, f t := by
  have hpi := Real.pi_pos
  have h0 : (0 : ℝ) ∈ Set.uIcc (-π) π := Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
  have h1 : IntervalIntegrable f MeasureTheory.volume (-π) 0 :=
    hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc h0)
  have h2 : IntervalIntegrable f MeasureTheory.volume 0 π :=
    hint.mono_set (Set.uIcc_subset_uIcc h0 Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have h3 : ∫ t in (-π)..0, f t = ∫ t in (0 : ℝ)..π, f t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) f
    rw [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t _ => hf t
  rw [h3]; ring

theorem symb_neg₁ (μ θ₁ θ₂ : ℝ) : symb μ (-θ₁) θ₂ = symb μ θ₁ θ₂ := by
  simp [symb, neg_div, Real.sin_neg]

theorem symb_neg₂ (μ θ₁ θ₂ : ℝ) : symb μ θ₁ (-θ₂) = symb μ θ₁ θ₂ := by
  simp [symb, neg_div, Real.sin_neg]

theorem continuous_inv_symb₂ {μ : ℝ} (hμ : 0 < μ) (θ₁ : ℝ) :
    Continuous fun θ₂ => 1 / symb μ θ₁ θ₂ :=
  continuous_const.div (by unfold symb; fun_prop) (fun _ => (symb_pos hμ _ _).ne')

theorem continuous_inner_symb {μ : ℝ} (hμ : 0 < μ) (c d : ℝ) :
    Continuous fun θ₁ => ∫ θ₂ in c..d, 1 / symb μ θ₁ θ₂ :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun θ₁ θ₂ => 1 / symb μ θ₁ θ₂) (continuous_inv_symb hμ) c d

/-- **`freeVar` over the quarter square**: freeVar = (1/π²) ∫_0^π ∫_0^π 1/w (m₀ ≠ 0). -/
theorem freeVar_eq_quarter {m₀ : ℝ} (hm : m₀ ≠ 0) :
    freeVar n m₀ = 1 / π ^ 2 *
      ∫ θ₁ in (0 : ℝ)..π, ∫ θ₂ in (0 : ℝ)..π, 1 / symb (m₀ ^ 2 * spacing n ^ 2) θ₁ θ₂ := by
  have hμ : 0 < m₀ ^ 2 * spacing n ^ 2 := by have := spacing_pos n; positivity
  set μ := m₀ ^ 2 * spacing n ^ 2 with hμdef
  show (2 * π)⁻¹ ^ 2 * ∫ θ₁ in (-π)..π, ∫ θ₂ in (-π)..π, 1 / symb μ θ₁ θ₂ = _
  have hin : ∀ θ₁, ∫ θ₂ in (-π)..π, 1 / symb μ θ₁ θ₂ = 2 * ∫ θ₂ in (0 : ℝ)..π, 1 / symb μ θ₁ θ₂ :=
    fun θ₁ => integral_even_pi (fun t => by simp only [symb_neg₂])
      ((continuous_inv_symb₂ hμ θ₁).intervalIntegrable _ _)
  simp_rw [hin]
  rw [integral_even_pi (fun t => by simp only [symb_neg₁])
    (((continuous_inner_symb hμ 0 π).const_mul 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **Boundary-strip bound at the centre of an odd box.** With a = h/2 = π/(2(M+1)) and
w the symbol at μ = m₀²ε²:
freeVar − specVar (2M+1) μ M M ≤ (1/π²)(∫_0^a ∫_0^π 1/w + ∫_0^π ∫_0^a 1/w).
(The two strips are equal by the symmetry θ₁ ↔ θ₂; that swap is not formalized.) -/
theorem freeVar_sub_specVar_centre_le {m₀ : ℝ} (hm : m₀ ≠ 0) (M : ℕ) (hM : M < 2 * M + 1) :
    freeVar n m₀ - specVar (2 * M + 1) (m₀ ^ 2 * spacing n ^ 2) ⟨M, hM⟩ ⟨M, hM⟩ ≤
      1 / π ^ 2 * ((∫ θ₁ in (0 : ℝ)..(midNode M 0), ∫ θ₂ in (0 : ℝ)..π,
          1 / symb (m₀ ^ 2 * spacing n ^ 2) θ₁ θ₂)
        + ∫ θ₁ in (0 : ℝ)..π, ∫ θ₂ in (0 : ℝ)..(midNode M 0),
          1 / symb (m₀ ^ 2 * spacing n ^ 2) θ₁ θ₂) := by
  have hμ : 0 < m₀ ^ 2 * spacing n ^ 2 := by have := spacing_pos n; positivity
  have hlow := specVar_centre_ge M hμ hM
  rw [freeVar_eq_quarter hm]
  set μ := m₀ ^ 2 * spacing n ^ 2 with hμdef
  set a := midNode M 0 with ha
  have ha0 : 0 ≤ a := midNode_nonneg M 0
  have haπ : a ≤ π := midNode_le_pi M 0 (Nat.zero_le _)
  have hI : ∀ c d e f : ℝ, IntervalIntegrable (fun θ₁ => ∫ θ₂ in c..d, 1 / symb μ θ₁ θ₂)
      MeasureTheory.volume e f := fun c d e f => (continuous_inner_symb hμ c d).intervalIntegrable _ _
  have hJ : ∀ θ₁ e f : ℝ, IntervalIntegrable (fun θ₂ => 1 / symb μ θ₁ θ₂)
      MeasureTheory.volume e f := fun θ₁ e f => (continuous_inv_symb₂ hμ θ₁).intervalIntegrable _ _
  have hpos : ∀ θ₁ θ₂, 0 ≤ 1 / symb μ θ₁ θ₂ := fun _ _ => (one_div_pos.mpr (symb_pos hμ _ _)).le
  -- split the outer integral at a
  have s1 : ∫ θ₁ in (0 : ℝ)..π, ∫ θ₂ in (0 : ℝ)..π, 1 / symb μ θ₁ θ₂ =
      (∫ θ₁ in (0 : ℝ)..a, ∫ θ₂ in (0 : ℝ)..π, 1 / symb μ θ₁ θ₂)
        + ∫ θ₁ in a..π, ∫ θ₂ in (0 : ℝ)..π, 1 / symb μ θ₁ θ₂ :=
    (intervalIntegral.integral_add_adjacent_intervals (hI _ _ _ _) (hI _ _ _ _)).symm
  -- split the inner integral at a
  have s2 : ∫ θ₁ in a..π, ∫ θ₂ in (0 : ℝ)..π, 1 / symb μ θ₁ θ₂ =
      (∫ θ₁ in a..π, ∫ θ₂ in (0 : ℝ)..a, 1 / symb μ θ₁ θ₂)
        + ∫ θ₁ in a..π, ∫ θ₂ in a..π, 1 / symb μ θ₁ θ₂ := by
    rw [← intervalIntegral.integral_add (hI _ _ _ _) (hI _ _ _ _)]
    exact intervalIntegral.integral_congr fun θ₁ _ =>
      (intervalIntegral.integral_add_adjacent_intervals (hJ _ _ _) (hJ _ _ _)).symm
  -- the piece over [a, π] × [0, a] is at most the full strip [0, π] × [0, a]
  have s3 : ∫ θ₁ in a..π, ∫ θ₂ in (0 : ℝ)..a, 1 / symb μ θ₁ θ₂ ≤
      ∫ θ₁ in (0 : ℝ)..π, ∫ θ₂ in (0 : ℝ)..a, 1 / symb μ θ₁ θ₂ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI _ _ 0 a) (hI _ _ a π)]
    have : 0 ≤ ∫ θ₁ in (0 : ℝ)..a, ∫ θ₂ in (0 : ℝ)..a, 1 / symb μ θ₁ θ₂ :=
      intervalIntegral.integral_nonneg ha0 fun θ₁ _ =>
        intervalIntegral.integral_nonneg ha0 fun θ₂ _ => hpos _ _
    linarith
  have hπ : 0 < 1 / π ^ 2 := by have := Real.pi_pos; positivity
  rw [s1, s2]
  nlinarith

end PP2Target
