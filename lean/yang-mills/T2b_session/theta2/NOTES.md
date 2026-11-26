# θ-2 notes: non-sharp tools for the θ-route (26 Nov 2026)

Labels:
- PROVED = checked here line by line.
- STD = standard, from the literature.
- NUM = numerical.
- HEUR = heuristic.

Files in this directory:
- `cw_terms.py`, `cw_Tbound.py`: Curie–Weiss φ⁴, exact in N via one-dimensional Hubbard–Stratonovich quadrature.
- `rw1site.py`: one-site checks of the random-walk identities.

**Conventions.** Lattice units, the weight of the draft, and an arbitrary vertex-transitive ferromagnetic graph. The field is H = ε²h and b = λε². Write
- S := Σ_y⟨φ_0;φ_y²⟩ = ∂_H⟨φ_0²⟩ = −∂_a m;
- χ = Σ_x⟨φ_0;φ_x⟩.

The exact lattice identity (EOM 4m + H = 2am + 4b⟨φ³⟩, plus the Maxwell relation) is

  m − Hχ = 4b m² (∂_H R + S).   (I)

The θ-target (θ-1 Form I) in lattice units is m − Hχ ≤ C' b m^θ S on {m ≤ s₀}, with C' independent of ε, L and h.

## 0. What "power gain over the trivial size" means — a correction

The trivial size O(χ/m) of the terms of ∂_H R is compared with m^{θ−2}·∂_H⟨φ²⟩. That comparison assumes ∂_H⟨φ²⟩ = S ≈ 2mχ, which is the Gaussian value. Exactly, S = U3 + 2mχ with U3 = Σu3(00x) ≤ 0.

**In the flip regime** (torus, μ < μ_c, h ~ 1/χ; this is where θ-1 shows (H_θ) is used, at h ≤ 3s₀/χ), the term U3 cancels 2mχ up to O(1).
- In the zero-mode picture φ ≈ σM + local, with x = h|T|M and t = tanh x:
  - mU4 = −2|T|M⁵t(1−t²)(1−3t²);
  - −χu3 = +2|T|M⁵t(1−t²)²;
  - 2m²U3 = −4|T|M⁵t³(1−t²).
- The three terms sum to 0 at order |T|, while S = O(1) (local).

NUM, Curie–Weiss with a = 1, b = 0.5, J = 4 (`cw_terms.py`):

| N | x | mU4 | 2m²U3 | −χu3 | sum | S | 2mχ |
|---|---|---|---|---|---|---|---|
| 64 | 1.0 | 3.44 | −6.93 | 3.26 | −0.230 | 1.25 | 14.2 |
| 1024 | 1.0 | 65.4 | −124.3 | 58.7 | −0.190 | 1.115 | 234 |
| 4096 | 1.0 | 263.9 | −499.5 | 235.4 | −0.189 | 1.111 | 936 |
| 4096 | 0.3 | −290.1 | −53.7 | 343.8 | −0.014 | 0.514 | 715 |

Identity (I) is reproduced to all digits in the same runs.

**Consequence.** In the flip regime the slack that (H_θ) grants is K m^θ S = O(m^θ). The individual terms are O(|T|).
- The gain needed over a termwise estimate is m^θ/|T|, a **volume** factor, not a power of m.
- So the θ-weakening does not relax the flip-regime difficulty for any method that bounds U4, U3 and u3 separately.
- It does relax it for methods that work with the PDE quantities m − hχ and −∂_μm directly. These are O(1) in the flip regime. They are also what θ-1's integrated Forms IV and V use.

Also, the volume-summed u4 is positive in a field: mU4 > 0 at x = 1 above. For a single Ising spin, u4 = −2sech²H(1 − 3tanh²H) > 0 once tanh²H > 1/3 (exact). So there is no "Lebowitz in a field".

## 1. ABF (J. Stat. Phys. 47, 1987) — fails by the factor 1/b, uniformly in θ

The PDF is not reachable by curl (proxy 403). It was read through WebFetch, from OCR. The formulas are as transcribed, and the equation numbers should be re-checked by eye.

- **Ising, (1.9)/(3.1):** M ≤ tanh(βh)∂M/∂(βh) + M³ + M²β∂M/∂β.
- **GS class, (1.10)/(4.13):** M ≲ βh z + (βhM² + β|J|M³) + (βhM + β|J|M²)∂M/∂β, with z = ∂M/∂(βh).
  - ∂_β is taken at fixed βh and fixed single-site measure.
  - "≲" hides constants. The fetch says they depend on p₀ only through S₂ = ∫φ²dp₀ (Lemma 5.2) and the GS block coupling.
  - No b-dependent prefactor appears.

**Scaling (PROVED, algebra).** In the draft's variables, ∂_β m = Σ_{⟨xy⟩}⟨φ_0;φ_xφ_y⟩. Using φ_xφ_y = ½(φ_x² + φ_y²) − ½(φ_x − φ_y)²:
- the first part is 2S = 4ε⁻²(−∂_μm);
- the second part is a kinetic-term derivative. In the continuum it is O(log ε⁻¹)(−∂_μm) + O(1), through c_ε ∝ 1/Z.

So the ABF term is β|J|M²∂_βM ≈ 4ε⁻²m²(−∂_μm). Identity (I) carries 8λm²(−∂_μm) = 8b·ε⁻²m²(−∂_μm).
- **Loss factor:** ≈ 1/(2b) = 1/(2λε²), times ABF's unspecified constant.
- **The θ-weakening cannot absorb it.** Replacing m² by C m^θ gains (m/s₀)^{θ−2}, which does not depend on ε. Absorbing the loss would need m^{2−θ} ≲ λε², i.e. it would work only on {m ≲ (λε²)^{1/(2−θ)}}, which shrinks to nothing.
- **Plus-state check.** In the plus state ABF gives −∂_μ(M²) ≳ ε², which is vacuous.
- **Why this is structural (HEUR).** Random currents and GS blocks never see b explicitly. For the Gaussian case b = 0 the inequality holds trivially, because m = hχ. Nothing forces the prefactor to vanish with the non-Gaussianity.

## 2. Termwise correlation inequalities and route (b)

The signs that are available: u2 ≥ 0 (GKS), u3 ≤ 0 in a field (GHS, EMN), u4 ≤ 0 at h = 0 only (Lebowitz), the BFS/Aizenman tree bound u4 ≥ −tree (a lower bound), and Newman's Gaussian moment bounds (h = 0).

The bad term −χu3(000) needs an **upper** bound on |u3|. The term mU4 needs an **upper** bound on u4 in a field. Neither is available. Even if both were, §0 shows that termwise use loses |T|.

**Route (b) is circular at the identity level (PROVED).**
- The EOM gives 4λ⟨:φ_0³:⟩ = h − μm. So ∂_h⟨:φ_0³:⟩ = (1 − μχ)/(4λ) exactly.
- Then ∂_h(⟨:φ³:⟩/m) = [m(1 − μχ) − (h − μm)χ]/(4λm²) = (m − hχ)/(4λm²).
- Any split of this into "∂_h⟨:φ³:⟩/m" and "⟨:φ³:⟩χ/m²", each bounded by Nelson-type Wick bounds, loses the cancellation of μmχ.
  - In the Gaussian-like regime the loss is a factor ≈ λ|μ|m^{−θ}.
  - In the flip regime it is a factor ~ |T|.
- Nelson bounds do make u3(000) = ⟨:(φ−m)³:⟩ ε-uniform. But in the flip regime u3 ≈ −2M³t(1−t²), which is non-perturbative and O(1), not O(λm).

## 3. Random-walk (BFS–Symanzik) route — the only tool found with the right λ prefactor

### Setup
- Any finite graph, J_xy ≥ 0, uniform H ≥ 0.
- Site weight e^{−aφ²−bφ⁴} = g(φ²/2) with g(s) = e^{−2as−4bs²}.
- Z(t) := ∫∏dφ e^{Σ_{xy}J_{xy}φ_xφ_y + HΣφ} ∏_x g(φ_x²/2 + t_x), and G(s) = ∫_0^∞ g(s+τ)dτ.

Integrate by parts, using ∂_φ G(φ²/2 + t) = −φ g(φ²/2 + t), and iterate (BFS 1982 with a field; STD). This gives the following.
- m = ∫dW_0 Z(t_ω)/Z, where dW_0 is the positive measure on walks from 0 that end at the field. Steps carry weight J, each visit carries a Lebesgue local time, and the final step carries weight H. The measure dW_0 does not depend on a or b.
- ⟨φ_0φ_x⟩ = A_x + B_x, where:
  - B_x = ∫∫dW_0(ω₁)dW_x(ω₂) Z(t₁+t₂)/Z;
  - A_x is the walks 0 → x;
  - m = HΣ_xA_x.

### Results

**RW0 (PROVED; NUM-checked on one site).**

  m − Hχ = H Σ_x ∫∫ dW_0 dW_x [Z(t₁)Z(t₂) − Z(t₁+t₂)Z]/Z².

**Factorisation (PROVED).** g(s+t₁+t₂)g(s) = g(s+t₁)g(s+t₂)e^{−8b t₁t₂}. Hence

  Z(t₁+t₂)/Z = e^{−8b(t₁,t₂)}⟨E₁E₂⟩,

with E_t := ∏_x g(s_x+t_x)/g(s_x). Each E_t is decreasing in every |φ_x|. The |φ|-marginal is MTP2: its log-density has ∂_{r_x}∂_{r_y} ≥ 0 by GKS II with H ≥ 0. So FKG gives ⟨E₁E₂⟩ ≥ ⟨E₁⟩⟨E₂⟩.

**RW1 (PROVED).** Using 1 − e^{−u} ≤ u, and with τ_x(z) := ∫dW_x (Z(t)/Z) t_z and T := Σ_zτ_0(z),

  0 ≤ m − Hχ ≤ 8bH Σ_{x,z} τ_0(z)τ_x(z) = 8bH T².

This is ε-uniform: in continuum units it reads m − hχ ≤ 8λhT_c².

**RW2 (PROVED).** −∂_{a_z}m = ⟨φ_0;φ_z²⟩ = 2τ_0(z) − 2Δ_z, where

  Δ_z := ∫dW_0 (Z(t)/Z)(⟨s_z⟩ − ⟨s_z⟩_t) ≥ 0

by FKG, since ⟨·⟩_t ∝ E_t·P. So T = S/2 + Δ.

**RW3 (PROVED from (I), RW1, RW2 and GHS).** GHS gives hS ≤ 2hmχ ≤ 2m². Then

  ∂_H R ≤ S(HS − 2m²)/(2m²) + 2HΔ(S+Δ)/m² ≤ 2HΔ(S+Δ)/m².

**Corollary (PROVED).** Define the screening ratio κ := Δ/T ∈ [0,1). If κ ≤ κ₀ < 1 on a region, then L holds there with

  K = κ₀(2−κ₀)/(1−κ₀)².

- At first order κ ≈ 2λ∫⟨:φ²:;:φ²:⟩, which is a weak-coupling condition (HEUR).
- At the Gaussian point RW1 is sharp. NUM, one site: 8bhT²/(m − hχ) = 1.02 at (a,b) = (2, 0.02), and 1.15 at (2, 0.2).

NUM, one site (`rw1site.py`): RW0 matches to grid accuracy. The ratio 8bhT²/(m − hχ) and the ratio T/(S/2) both grow with the well depth:

| a (b = 1) | 1 | 0 | −1 | −2 | −4 |
|---|---|---|---|---|---|
| 8bhT²/(m − hχ) | 1.5 | 1.8 | 2.3 | 3.1 | 6.6 |
| T/(S/2) | 1.13 | 1.23 | 1.42 | 1.86 | 4.7 |

In the Ising limit, S → 0 at fixed T.

### Where it fails: the flip regime

RW1 gives T ≥ √((m − Hχ)/(8bH)) (PROVED). With the flip asymptotics m − hχ ≈ M(t − x sech²x) and h = x/(|T|M), this means

  T/S ≥ c √(|T|/λ) → ∞,

so the screening ratio κ = Δ/T → 1.

NUM, Curie–Weiss (`cw_Tbound.py`): T_lower/(S/2) = 2.4, 5.6, 11.4, 23.0, 46.0 for N = 64, …, 16384 at x = 1. The ratio to √N is constant at 0.36.

**HEUR on actual sizes.** Walks to the field have local time ~ volume (T ~ mχ). The pair overlap is u ~ λ|T| ≫ 1, and it is compensated by an environment factor ⟨E₁E₂⟩/(⟨E₁⟩⟨E₂⟩) ~ e^{u}, which RW1 discards.
- RW3 with θ < 2 would need H·T·κ ≲ m^θ(1−κ). With 1−κ ≈ S/(2T) ~ 1/|T| and HT ~ m², this fails by a factor ~ |T|.
- It would survive only if T ~ √|T|. No mechanism for that was found.
- In the plus-state limit (h → 0 at large x), any bound reduces to M ≤ C M^θ(−∂_μM). This requires the lower bound on −∂_μM that is the conclusion itself. RW cannot supply it, because S = 2T − 2Δ with Δ ≈ T is exactly the statement that −∂_μ m is not screened.

## 4. Bottom line

No proof was found.

| tool | failure | size of failure |
|---|---|---|
| ABF | b-free prefactor | factor ≈ 1/(2λε²), any θ |
| termwise GKS/GHS/Lebowitz/BFS/Nelson | volume-order cancellation in the flip regime | factor |T|·m^{−θ} |
| RW (BFS) | screening κ → 1 in the flip regime | factor ≥ √(|T|/λ), and ~ |T| heuristically |

Positive by-products, all PROVED:
- RW0–RW3: an exact random-walk formula for m − hχ, and the ε-uniform bound m − hχ ≤ 8λhT_c².
- L with explicit K under the screening condition κ < 1, which in practice means weak coupling.

What survives: only methods that keep m − hχ and −∂_μm as whole objects and exploit the zero-mode (bump/plateau) structure of the law of the torus magnetisation. These are θ-1's Forms IV and V, for θ-3.
- Caution for Form IV: n(v) = E[N₂ | M = v] is roughly flat on the interface plateau. So "n(v) − κv² nondecreasing", which would sign Cov(v, n), fails there (HEUR).
- The θ-room has to come from the bump region, as in θ-1 §5(c).
