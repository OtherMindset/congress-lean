import LongTable.R_PP2WickSplitB

/-!
Posted copy of congress-lean lean/yang-mills/PP7_parallel_round1/PP2Chaos.lean (same content; only the imports are renamed).
Yang-Mills table, Long Table. Claude council, P(phi)_2 direction. Node M5e, session 1:
moment (hypercontractive-type) bounds for Wick polynomials of degree ≤ 4 in finitely many
independent standard Gaussians, for Nelson's estimate.

ROUTE (chosen this session): Nelson-type hypercontractivity L² → L^{2m} with a SMALL,
m-dependent contraction parameter ρ = ρ_m, proved by induction on the number of variables.
  Statement S(n): for c : (Fin n → Fin 5) → ℝ, F_c(x) = Σ_α c_α Π_i He_{α_i}(x_i) and
  (T_ρ c)_α = ρ^{|α|} c_α,   E_{γ^n}[F_{T_ρ c}^{2m}] ≤ (Σ_α α! c_α²)^m = (E F_c²)^m.
  * 1-D step (this file, `oneDim_moment`): E_γ[(Σ_{k≤4} ρ^k b_k He_k)^{2m+2}] ≤ (Σ_k k! b_k²)^{m+1}
    whenever (m+1)(2m+1) ρ² E[P(1+ρ²P)^m] ≤ 1, P = Σ_{k=1}^4 He_k²/k!. Proof: second-order
    Taylor bound (u+e)^{N} ≤ u^N + N u^{N−1} e + C(N,2) e² (|u|+|e|)^{N−2} (`taylor_two_le`,
    elementary induction), E e = 0, weighted Cauchy–Schwarz e² ≤ ρ² s P, and
    (|u|+|e|)² ≤ (u²+s)(1+ρ²P). The constant in front of b_0^{2m+2} is exactly 1, which is
    what makes the n-variable induction close without a C^n loss.
  * Tensorization (next session): split x = (x₀, y) (`measurePreserving_piFinSuccAbove`),
    F_{T c}(x₀,y) = Σ_k ρ^k He_k(x₀) G_k(y), G_k = F_{T c_k}; apply the 1-D step for fixed y
    with b_k = G_k(y), then Minkowski in L^m(y) (`ENNReal.lintegral_Lp_add_le`) and S(n−1).
    Working with lintegral of nonnegative integrands (Tonelli) avoids n-dimensional
    integrability bookkeeping; only 1-D integrability (polynomials, `PolyFn.integrable`) is used.
  * Explicit ρ_m: P ≤ 4(1+x²)⁴ and P(1+ρ²P)^m ≤ 3P + (2(m+1)ρ²)^m P^{m+1}, Gaussian moments
    E x^{2j} = (2j−1)!! (`gaussian_moment_succ_succ`) give ρ_m^{-1} polynomial in m (≈ m^{9/2}): any
    polynomial growth suffices for Nelson (tail exp(−c (t/‖W‖₂)^{1/γ}) beats e^{C (log κ)²}).
  * Consequence: for F of chaos degree ≤ d (supported on |α| ≤ d),
    ‖F‖_{2m} ≤ ρ_m^{−d} ‖F‖₂ (apply S(n) to T_ρ^{−1} c). For d = 4 this is ‖W‖_q ≤ C q^{γ}‖W‖₂.
  Why not the alternatives: (A) as stated (L⁴ with ρ = 1/√3, then squaring) needs the sharp
  one-dimensional (2,4) inequality for ALL degrees (f² doubles the per-variable degree), which is
  full Gaussian hypercontractivity; here the per-variable degree stays ≤ 4 and ρ may be small.
  (B) Feynman-graph counting bounds E W^{2p} by graph sums Σ_x Π|C|, not by (E W²)^p, unless one
  adds L^p estimates on C — more work and model-specific; Isserlis is not in Mathlib.
  (C) E e^{tW} ≤ e^{c t² E W²} is false for degree-4 chaos (tails are exp(−c t^{1/2})).

FORMALIZED (this session):
* `taylor_two_abs`, `taylor_two_le`: |(u+e)^{n+2} − u^{n+2} − (n+2)u^{n+1}e| ≤
  ((n+2)(n+1)/2) e² (|u|+|e|)^n, for all real u, e and all n.
* `PolyFn` (functions that are polynomial evaluations) with closure lemmas, and
  `PolyFn.integrable`: every polynomial is integrable for the standard Gaussian.
* `integral_He`: E_γ He_k = 0 for 1 ≤ k ≤ 4 (He_k = `wickPow 1 k`).
* `cs4_weighted`, `weights_le`, `sq_err_le`: the weighted Cauchy–Schwarz step e² ≤ ρ² s P.
* `oneDim_moment` (main theorem of the session): the one-dimensional hypercontractive step
  E_γ[(Σ_{k≤4} ρ^k b_k He_k)^{2m+2}] ≤ (Σ_{k≤4} k! b_k²)^{m+1} for 0 ≤ ρ ≤ 1 and
  (m+1)(2m+1) ρ² E_γ[P (1 + ρ² P)^m] ≤ 1, all m and all b : Fin 5 → ℝ.

NOT formalized (remaining, estimate 2–4 sessions): an explicit admissible ρ_m (Gaussian moment
bounds, ~1 session); the n-variable tensorization S(n) (product measure split, Tonelli, Minkowski,
L² identity E F_c² = Σ α! c_α² from `wickPow_orthogonal`, ~1–2 sessions); the degree-d corollary
‖F‖_{2m} ≤ ρ_m^{−d}‖F‖₂ and the Markov tail bound P(|F| > t) ≤ exp(−c (t/‖F‖₂)^{1/γ})
(~½ session); expressing the lattice rough part V_r (Wick quartics of a correlated Gaussian field,
φ = A ξ) as a degree-≤ 4 polynomial in independent standard Gaussians ξ, i.e. as some F_c with
|α| ≤ 4 (~1 session; triangularity x^j ∈ span{He_k : k ≤ j}).

Toolchain: leanprover/lean4:v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

open MeasureTheory ProbabilityTheory NNReal Finset

noncomputable section

namespace PP2Chaos

open PP2Target

/-! ## A second-order Taylor bound for powers -/

/-- |(u+e)^{n+2} − u^{n+2} − (n+2) u^{n+1} e| ≤ ((n+2)(n+1)/2) e² (|u|+|e|)^n. -/
theorem taylor_two_abs (u e : ℝ) (n : ℕ) :
    |(u + e) ^ (n + 2) - u ^ (n + 2) - ((n : ℝ) + 2) * u ^ (n + 1) * e| ≤
      ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 * e ^ 2 * (|u| + |e|) ^ n := by
  induction n with
  | zero =>
    have h : (u + e) ^ (0 + 2) - u ^ (0 + 2) - (((0 : ℕ) : ℝ) + 2) * u ^ (0 + 1) * e = e ^ 2 := by
      push_cast; ring
    rw [h, abs_of_nonneg (sq_nonneg e)]
    simp
  | succ n ih =>
    have hrec : (u + e) ^ (n + 1 + 2) - u ^ (n + 1 + 2)
        - (((n + 1 : ℕ) : ℝ) + 2) * u ^ (n + 1 + 1) * e
        = (u + e) * ((u + e) ^ (n + 2) - u ^ (n + 2) - ((n : ℝ) + 2) * u ^ (n + 1) * e)
          + ((n : ℝ) + 2) * u ^ (n + 1) * e ^ 2 := by
      push_cast; ring
    rw [hrec]
    set R := (u + e) ^ (n + 2) - u ^ (n + 2) - ((n : ℝ) + 2) * u ^ (n + 1) * e
    have hS : 0 ≤ |u| + |e| := by positivity
    have h1 : |u + e| ≤ |u| + |e| := abs_add_le u e
    have h2 : |u| ^ (n + 1) ≤ (|u| + |e|) ^ (n + 1) :=
      pow_le_pow_left₀ (abs_nonneg u) (by linarith [abs_nonneg e]) _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc |(u + e) * R + ((n : ℝ) + 2) * u ^ (n + 1) * e ^ 2|
        ≤ |u + e| * |R| + ((n : ℝ) + 2) * |u| ^ (n + 1) * e ^ 2 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (sq_nonneg e),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)]
      _ ≤ (|u| + |e|) * (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 * e ^ 2 * (|u| + |e|) ^ n)
          + ((n : ℝ) + 2) * (|u| + |e|) ^ (n + 1) * e ^ 2 := by
          refine add_le_add (mul_le_mul h1 ih (abs_nonneg _) hS) ?_
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (by positivity)) (sq_nonneg e)
      _ = (((n + 1 : ℕ) : ℝ) + 2) * (((n + 1 : ℕ) : ℝ) + 1) / 2 * e ^ 2
            * (|u| + |e|) ^ (n + 1) := by
          push_cast; ring

theorem taylor_two_le (u e : ℝ) (n : ℕ) :
    (u + e) ^ (n + 2) ≤ u ^ (n + 2) + ((n : ℝ) + 2) * u ^ (n + 1) * e
      + ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 * e ^ 2 * (|u| + |e|) ^ n := by
  have := (abs_le.mp (taylor_two_abs u e n)).2
  linarith

/-! ## Polynomial functions and Gaussian integrability -/

/-- `f` is the evaluation map of a real polynomial. -/
def PolyFn (f : ℝ → ℝ) : Prop := ∃ q : Polynomial ℝ, ∀ x, f x = q.eval x

namespace PolyFn

theorem const (c : ℝ) : PolyFn (fun _ => c) := ⟨Polynomial.C c, fun _ => by simp⟩

theorem add {f g : ℝ → ℝ} (hf : PolyFn f) (hg : PolyFn g) : PolyFn (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

theorem mul {f g : ℝ → ℝ} (hf : PolyFn f) (hg : PolyFn g) : PolyFn (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

theorem pow {f : ℝ → ℝ} (hf : PolyFn f) (n : ℕ) : PolyFn (fun x => f x ^ n) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ n, fun x => by simp [hp]⟩

theorem const_mul {f : ℝ → ℝ} (c : ℝ) (hf : PolyFn f) : PolyFn (fun x => c * f x) :=
  (const c).mul hf

theorem div_const {f : ℝ → ℝ} (hf : PolyFn f) (c : ℝ) : PolyFn (fun x => f x / c) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p * Polynomial.C c⁻¹, fun x => by simp [hp, div_eq_mul_inv]⟩

theorem wickPow (c : ℝ) (k : ℕ) : PolyFn (fun x => PP2Target.wickPow c k x) :=
  ⟨∑ j ∈ range (k / 2 + 1), Polynomial.C ((-1 : ℝ) ^ j * (k.factorial : ℝ) /
      ((j.factorial : ℝ) * ((k - 2 * j).factorial : ℝ) * 2 ^ j) * c ^ j) *
      Polynomial.X ^ (k - 2 * j),
    fun x => by simp [PP2Target.wickPow, Polynomial.eval_finsetSum]⟩

/-- Every polynomial is integrable for the standard Gaussian. -/
theorem integrable {f : ℝ → ℝ} (hf : PolyFn f) : Integrable f (gaussianReal 0 1) := by
  obtain ⟨q, hq⟩ := hf
  have hfun : f = fun x => ∑ i ∈ range (q.natDegree + 1), q.coeff i * x ^ i := by
    funext x; rw [hq, Polynomial.eval_eq_sum_range]
  rw [hfun]
  exact integrable_finsetSum _ (fun i _ => (integrable_pow_gaussianReal 1 i).const_mul _)

end PolyFn

/-! ## The one-dimensional Hermite basis of degree ≤ 4 -/

/-- Probabilists' Hermite polynomial He_k = :x^k:_1. -/
def He (k : ℕ) (x : ℝ) : ℝ := wickPow 1 k x

theorem He_zero (x : ℝ) : He 0 x = 1 := wickPow_zero' 1 x

theorem He_polyFn (k : ℕ) : PolyFn (fun x => He k x) := PolyFn.wickPow 1 k

theorem integral_He (k : ℕ) (hk : k ≤ 4) (hk0 : k ≠ 0) :
    ∫ x, He k x ∂gaussianReal 0 1 = 0 := by
  have h := integral_wickPow_gaussianReal 1 k hk
  simp only [NNReal.coe_one] at h
  simpa [He, hk0] using h

/-- Σ_{k ≤ 4} ρ^k b_k He_k(x): the one-variable expansion, contracted by T_ρ. -/
def hpoly (ρ : ℝ) (b : Fin 5 → ℝ) (x : ℝ) : ℝ := ∑ k : Fin 5, ρ ^ (k : ℕ) * b k * He k x

/-- Σ_{k ≤ 4} k! b_k² = E_γ[(Σ b_k He_k)²]. -/
def hnorm (b : Fin 5 → ℝ) : ℝ := ∑ k : Fin 5, ((k : ℕ).factorial : ℝ) * b k ^ 2

/-- P = Σ_{k=1}^4 He_k²/k!. -/
def Pfun (x : ℝ) : ℝ := He 1 x ^ 2 + He 2 x ^ 2 / 2 + He 3 x ^ 2 / 6 + He 4 x ^ 2 / 24

theorem Pfun_nonneg (x : ℝ) : 0 ≤ Pfun x := by unfold Pfun; positivity

theorem Pfun_polyFn : PolyFn Pfun :=
  ((((He_polyFn 1).pow 2).add (((He_polyFn 2).pow 2).div_const 2)).add
    (((He_polyFn 3).pow 2).div_const 6)).add (((He_polyFn 4).pow 2).div_const 24)

theorem hpoly_eq (ρ : ℝ) (b : Fin 5 → ℝ) (x : ℝ) :
    hpoly ρ b x = b 0 + (ρ * b 1 * He 1 x + ρ ^ 2 * b 2 * He 2 x + ρ ^ 3 * b 3 * He 3 x
      + ρ ^ 4 * b 4 * He 4 x) := by
  simp [hpoly, Fin.sum_univ_five, He_zero]
  ring

theorem hnorm_eq (b : Fin 5 → ℝ) :
    hnorm b = b 0 ^ 2 + (b 1 ^ 2 + 2 * b 2 ^ 2 + 6 * b 3 ^ 2 + 24 * b 4 ^ 2) := by
  simp [hnorm, Fin.sum_univ_five, Nat.factorial]
  ring

/-! ## The weighted Cauchy–Schwarz step -/

theorem cs4_weighted (A1 A2 A3 A4 c1 c2 c3 c4 : ℝ) :
    (A1 * c1 + A2 * c2 + A3 * c3 + A4 * c4) ^ 2 ≤
      (A1 ^ 2 + 2 * A2 ^ 2 + 6 * A3 ^ 2 + 24 * A4 ^ 2) *
        (c1 ^ 2 + c2 ^ 2 / 2 + c3 ^ 2 / 6 + c4 ^ 2 / 24) := by
  nlinarith [sq_nonneg (A1 * c2 - 2 * A2 * c1), sq_nonneg (A1 * c3 - 6 * A3 * c1),
    sq_nonneg (A1 * c4 - 24 * A4 * c1), sq_nonneg (2 * A2 * c3 - 6 * A3 * c2),
    sq_nonneg (2 * A2 * c4 - 24 * A4 * c2), sq_nonneg (6 * A3 * c4 - 24 * A4 * c3)]

theorem weights_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (b1 b2 b3 b4 : ℝ) :
    (ρ * b1) ^ 2 + 2 * (ρ ^ 2 * b2) ^ 2 + 6 * (ρ ^ 3 * b3) ^ 2 + 24 * (ρ ^ 4 * b4) ^ 2 ≤
      ρ ^ 2 * (b1 ^ 2 + 2 * b2 ^ 2 + 6 * b3 ^ 2 + 24 * b4 ^ 2) := by
  have h2 : ρ ^ 2 ≤ 1 := by nlinarith
  have h20 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have h4 : ρ ^ 4 ≤ ρ ^ 2 := by nlinarith
  have h6 : ρ ^ 6 ≤ ρ ^ 2 := by nlinarith
  have h8 : ρ ^ 8 ≤ ρ ^ 2 := by nlinarith
  have e2 : (ρ ^ 2 * b2) ^ 2 = ρ ^ 4 * b2 ^ 2 := by ring
  have e3 : (ρ ^ 3 * b3) ^ 2 = ρ ^ 6 * b3 ^ 2 := by ring
  have e4 : (ρ ^ 4 * b4) ^ 2 = ρ ^ 8 * b4 ^ 2 := by ring
  rw [e2, e3, e4]
  nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg b2),
    mul_le_mul_of_nonneg_right h6 (sq_nonneg b3), mul_le_mul_of_nonneg_right h8 (sq_nonneg b4)]

/-- The error term e = Σ_{k=1}^4 ρ^k b_k He_k satisfies e² ≤ ρ² s P. -/
theorem sq_err_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (b : Fin 5 → ℝ) (x : ℝ) :
    (ρ * b 1 * He 1 x + ρ ^ 2 * b 2 * He 2 x + ρ ^ 3 * b 3 * He 3 x + ρ ^ 4 * b 4 * He 4 x) ^ 2
      ≤ ρ ^ 2 * (b 1 ^ 2 + 2 * b 2 ^ 2 + 6 * b 3 ^ 2 + 24 * b 4 ^ 2) * Pfun x := by
  have h := cs4_weighted (ρ * b 1) (ρ ^ 2 * b 2) (ρ ^ 3 * b 3) (ρ ^ 4 * b 4)
    (He 1 x) (He 2 x) (He 3 x) (He 4 x)
  have hw := weights_le ρ hρ0 hρ1 (b 1) (b 2) (b 3) (b 4)
  have hP := Pfun_nonneg x
  unfold Pfun at hP ⊢
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right hw hP

/-- (|u| + |e|)² ≤ (u² + s)(1 + r) when e² ≤ s r, s, r ≥ 0. -/
theorem sum_abs_sq_le (u e s r : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ r) (he : e ^ 2 ≤ s * r) :
    (|u| + |e|) ^ 2 ≤ (u ^ 2 + s) * (1 + r) := by
  have ha : |u| ^ 2 = u ^ 2 := sq_abs u
  have hc : |e| ^ 2 = e ^ 2 := sq_abs e
  have hc2 : |e| ^ 2 ≤ s * r := hc ▸ he
  have hac : 2 * |u| * |e| ≤ |u| ^ 2 * r + s := by
    have h1 : (2 * |u| * |e|) ^ 2 ≤ (|u| ^ 2 * r + s) ^ 2 := by
      nlinarith [sq_nonneg (|u| ^ 2 * r - s), mul_le_mul_of_nonneg_left hc2 (sq_nonneg |u|)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  nlinarith

/-! ## The pointwise bound -/

theorem pointwise_bound (m : ℕ) (ρ u s e P : ℝ) (hs : 0 ≤ s) (hP : 0 ≤ P)
    (hCS : e ^ 2 ≤ ρ ^ 2 * s * P) :
    (u + e) ^ (2 * m + 2) ≤ u ^ (2 * m + 2) + (2 * (m : ℝ) + 2) * u ^ (2 * m + 1) * e
      + ((m : ℝ) + 1) * (2 * m + 1) * (ρ ^ 2 * s * (u ^ 2 + s) ^ m * (P * (1 + ρ ^ 2 * P) ^ m)) := by
  have T := taylor_two_le u e (2 * m)
  have AB : (|u| + |e|) ^ 2 ≤ (u ^ 2 + s) * (1 + ρ ^ 2 * P) :=
    sum_abs_sq_le u e s (ρ ^ 2 * P) hs (by positivity) (by linarith)
  have key : e ^ 2 * (|u| + |e|) ^ (2 * m) ≤ ρ ^ 2 * s * P * ((u ^ 2 + s) * (1 + ρ ^ 2 * P)) ^ m := by
    rw [pow_mul]
    exact mul_le_mul hCS (pow_le_pow_left₀ (sq_nonneg _) AB m) (by positivity) (by positivity)
  have hY : ρ ^ 2 * s * P * ((u ^ 2 + s) * (1 + ρ ^ 2 * P)) ^ m
      = ρ ^ 2 * s * (u ^ 2 + s) ^ m * (P * (1 + ρ ^ 2 * P) ^ m) := by
    rw [mul_pow]; ring
  have key2 : ((m : ℝ) + 1) * (2 * m + 1) * (e ^ 2 * (|u| + |e|) ^ (2 * m)) ≤
      ((m : ℝ) + 1) * (2 * m + 1) * (ρ ^ 2 * s * (u ^ 2 + s) ^ m * (P * (1 + ρ ^ 2 * P) ^ m)) := by
    rw [← hY]; exact mul_le_mul_of_nonneg_left key (by positivity)
  push_cast at T
  linear_combination T + key2

/-! ## The one-dimensional hypercontractive step -/

/-- **One-dimensional step of the hypercontractive moment bound.** For the standard Gaussian γ,
0 ≤ ρ ≤ 1 and (m+1)(2m+1) ρ² E_γ[P (1+ρ²P)^m] ≤ 1 (P = Σ_{k=1}^4 He_k²/k!), every
b : Fin 5 → ℝ satisfies E_γ[(Σ_{k≤4} ρ^k b_k He_k)^{2m+2}] ≤ (Σ_{k≤4} k! b_k²)^{m+1}. -/
theorem oneDim_moment (m : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcond : ((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 *
      ∫ x, Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m ∂gaussianReal 0 1 ≤ 1)
    (b : Fin 5 → ℝ) :
    ∫ x, hpoly ρ b x ^ (2 * m + 2) ∂gaussianReal 0 1 ≤ hnorm b ^ (m + 1) := by
  set u := b 0
  set s := b 1 ^ 2 + 2 * b 2 ^ 2 + 6 * b 3 ^ 2 + 24 * b 4 ^ 2 with hs_def
  set e : ℝ → ℝ := fun x =>
    ρ * b 1 * He 1 x + ρ ^ 2 * b 2 * He 2 x + ρ ^ 3 * b 3 * He 3 x + ρ ^ 4 * b 4 * He 4 x
    with he_def
  set Q : ℝ → ℝ := fun x => Pfun x * (1 + ρ ^ 2 * Pfun x) ^ m with hQ_def
  set K : ℝ := ((m : ℝ) + 1) * (2 * m + 1) * (ρ ^ 2 * s * (u ^ 2 + s) ^ m) with hK_def
  have hs : 0 ≤ s := by positivity
  have he_poly : PolyFn e :=
    ((((He_polyFn 1).const_mul (ρ * b 1)).add ((He_polyFn 2).const_mul (ρ ^ 2 * b 2))).add
      ((He_polyFn 3).const_mul (ρ ^ 3 * b 3))).add ((He_polyFn 4).const_mul (ρ ^ 4 * b 4))
  have hQ_poly : PolyFn Q :=
    Pfun_polyFn.mul (((PolyFn.const 1).add (Pfun_polyFn.const_mul (ρ ^ 2))).pow m)
  have hint_e : ∫ x, e x ∂gaussianReal 0 1 = 0 := by
    have p1 := (He_polyFn 1).const_mul (ρ * b 1)
    have p2 := (He_polyFn 2).const_mul (ρ ^ 2 * b 2)
    have p3 := (He_polyFn 3).const_mul (ρ ^ 3 * b 3)
    have p4 := (He_polyFn 4).const_mul (ρ ^ 4 * b 4)
    simp only [he_def]
    rw [integral_add ((p1.add p2).add p3).integrable p4.integrable,
      integral_add (p1.add p2).integrable p3.integrable,
      integral_add p1.integrable p2.integrable,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_He 1 (by norm_num) (by norm_num), integral_He 2 (by norm_num) (by norm_num),
      integral_He 3 (by norm_num) (by norm_num), integral_He 4 (by norm_num) (by norm_num)]
    ring
  -- the pointwise bound
  have hpt : ∀ x, hpoly ρ b x ^ (2 * m + 2) ≤
      u ^ (2 * m + 2) + (2 * (m : ℝ) + 2) * u ^ (2 * m + 1) * e x + K * Q x := by
    intro x
    rw [hpoly_eq]
    have := pointwise_bound m ρ u s (e x) (Pfun x) hs (Pfun_nonneg x)
      (sq_err_le ρ hρ0 hρ1 b x)
    simp only [hK_def, hQ_def]
    linarith
  have hL : PolyFn (fun x => hpoly ρ b x ^ (2 * m + 2)) := by
    have : (fun x => hpoly ρ b x ^ (2 * m + 2)) = fun x => (u + e x) ^ (2 * m + 2) := by
      funext x; rw [hpoly_eq]
    rw [this]
    exact ((PolyFn.const u).add he_poly).pow _
  have hR1 : Integrable (fun x => u ^ (2 * m + 2) + (2 * (m : ℝ) + 2) * u ^ (2 * m + 1) * e x)
      (gaussianReal 0 1) :=
    ((PolyFn.const _).add (he_poly.const_mul _)).integrable
  have hR2 : Integrable (fun x => K * Q x) (gaussianReal 0 1) := (hQ_poly.const_mul K).integrable
  calc ∫ x, hpoly ρ b x ^ (2 * m + 2) ∂gaussianReal 0 1
      ≤ ∫ x, (u ^ (2 * m + 2) + (2 * (m : ℝ) + 2) * u ^ (2 * m + 1) * e x + K * Q x)
          ∂gaussianReal 0 1 :=
        integral_mono hL.integrable (hR1.add hR2) hpt
    _ = u ^ (2 * m + 2) + K * ∫ x, Q x ∂gaussianReal 0 1 := by
        rw [integral_add hR1 hR2, integral_add (integrable_const _) (he_poly.const_mul _).integrable,
          integral_const_mul, integral_const_mul, hint_e]
        simp
    _ ≤ u ^ (2 * m + 2) + s * (u ^ 2 + s) ^ m := by
        have hc : ((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 * ∫ x, Q x ∂gaussianReal 0 1 ≤ 1 := hcond
        have hA : 0 ≤ s * (u ^ 2 + s) ^ m := by positivity
        have : K * ∫ x, Q x ∂gaussianReal 0 1 =
            (s * (u ^ 2 + s) ^ m) *
              (((m : ℝ) + 1) * (2 * m + 1) * ρ ^ 2 * ∫ x, Q x ∂gaussianReal 0 1) := by
          rw [hK_def]; ring
        rw [this]
        nlinarith
    _ ≤ (u ^ 2 + s) ^ (m + 1) := by
        have h1 : u ^ (2 * m + 2) = (u ^ 2) ^ m * u ^ 2 := by rw [← pow_mul]; ring
        have h2 : (u ^ 2) ^ m ≤ (u ^ 2 + s) ^ m := pow_le_pow_left₀ (sq_nonneg u) (by linarith) m
        rw [h1, pow_succ (u ^ 2 + s) m]
        nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg u)]
    _ = hnorm b ^ (m + 1) := by rw [hnorm_eq]

end PP2Chaos
