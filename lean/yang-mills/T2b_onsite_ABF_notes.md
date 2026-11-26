# T2b — on-site ABF for lattice φ⁴₂: notes

**Conventions.** Λ_ε = εℤ² (torus, or the infinite-volume plus state at h>0). The weight is
exp(Σ_{⟨xy⟩}φ_xφ_y + ε²hΣφ_x) ∏ρ(dφ_x), with ρ(dφ) = e^{−aφ²−bφ⁴}dφ, a = 2+½ε²μ_bare, b = λε², and μ_bare = μ−12λc_ε (c_ε = Wick constant ~ (2π)⁻¹log ε⁻¹).
In the notation of GPPS [3, eqs. (1.2)–(1.4)] this is βJ=1, g=b, h_x=ε²h. So ∂_μ = ½ε²∂_a, and [3, Prop. 3.20] gives ∂_μm = −½ε²Σ_y⟨φ_0;φ_y²⟩ ≤ 0 (GKS II).

## 1. Switching identity for ⟨φ_0;φ_y²⟩ — PROVED at finite N; tangled limit PLAUSIBLE

In the Griffiths–Simon block picture [2, eqs. (2.3)–(2.4)], φ_y = α_NΣ_iσ_{y,i}, so φ_y² = α_N²(N + Σ_{i≠j}σ_{y,i}σ_{y,j}). The field couples to a ghost g. The Ising switching lemma [2, Lemma 3.3] gives the standard derivative identity ⟨σ_A;σ_uσ_v⟩ = Σ_±⟨σ_Aσ_u⟩⟨σ_vσ_g⟩P^{Au,vg}[u↮v] (for |A|=1 with the ghost). Applying it gives

(I1) ⟨φ_0;φ_y²⟩ = 2α_N² Σ_{i≠j} ⟨φ_0σ_{y,i}⟩⟨σ_{y,j}σ_g⟩ · P^{0(y,i),(y,j)g}[(y,i)↮(y,j)].

Here ↮ means "not connected", and it counts **intra-block** edges of the GS graph. Only finite-N Ising switching is used, so this is rigorous.

In the N→∞ limit, GPPS's tangled currents [3, Def. 3.10, Thm 3.12, Cor 3.15, Prop 3.17] should give

(I2) ⟨φ_0;φ_y²⟩ = 2⟨φ_0φ_y⟩⟨φ_y⟩ · P^{δ_0+δ_y, δ_y+δ_g}[y^A ↮ y^B in H(n_1,n_2,t)].

To derive it, take A=δ_0+δ_y, B=δ_y+δ_g and F = 1[y-labels disconnected] in Thm 3.12. The factor 2 assumes the tangling law is exchangeable in the two y-labels; this needs checking. The event says the current loop 0→y and the path y→ghost are **not tangled at y** and do not meet anywhere else.

**ε-check.** −∂_μm = ε²Σ_y⟨φ_0φ_y⟩ m P[·]. This is a Riemann sum with no stray powers of ε. In contrast, ∂_β = Σ_{bonds} is ε⁻²·(ε²Σ).

## 2. "λ in front of ⟨φ_0;φ_y²⟩" — FAILS as posed (Gaussian obstruction)

At λ=0 (Gaussian, which is in the GS class; tangling = uniform Wick pairing [3, Rem. 3.16]):
- ⟨φ_0;φ_y²⟩ = 2mG_T(0,y), so (I2) holds with P = G_T/(G_T+m²).
- So −∂_μm = mχ (with χ = ε²ΣG_T) is O(1). No λ can be extracted from the on-site derivative itself.
- A doubly visited site joins two current strands with probability 2/3 under uniform pairing (2 of the 3 pairings of four half-edges). So an "on-site pivotal visit" is **not** suppressed by λ.

Any ABF-type split m = P(i)+P(ii) with P(i) ≤ hχ has slack at λ=0, because m = hχ exactly for the Gaussian. Gaussian double currents give P(ii) > 0: the cluster of 0 has ≥2 ghost edges with positive probability. So **no bound P(ii) ≤ Cλ(…) can hold.** The λ has to come from an *exact* treatment of the field term, not from pivotality.

## 3. The exact identity that supplies λ — PROVED (all ε, exact)

Integrate by parts at site 0 (the density is smooth). ⟨Δ_εφ⟩=0 and Σ_yΔ_εG_T(0,y)=0 by translation invariance, and :φ³: = φ³−3c_εφ. This gives

(EOM) μm + 4λ⟨:φ_0³:⟩ = h, (EOM′) μχ + 4λ∂_h⟨:φ_0³:⟩ = 1.

Eliminating μ:

**(★) m − h∂_hm = 4λ m² ∂_h(⟨:φ_0³:⟩/m).**

This is exact and has the *true* λ in front, with no ε⁻² anywhere. (It is just m²∂_h(h/m) with h/m = μ + 4λT/m.)

We also have the Maxwell relation −∂_μm = ½∂_h⟨φ_0²⟩ (both are second derivatives of the pressure; translation invariance). Using ⟨:φ³:⟩ = ⟨φ:φ²:⟩−2c_εm,

**(★★) m − h∂_hm ≤ Cλm²(−∂_μm) ⟺ ∂_h R(h) ≤ (C/8 − 1)·∂_h⟨φ_0²⟩, where R(h) := ⟨φ_0;φ_0²⟩/⟨φ_0⟩**

(a same-site truncated ratio). In particular **C=8 ⟺ h↦R(h) is nonincreasing.**

- R = 2G_T(0,0) + u_3(0,0,0)/m diverges like 2c_ε, but ∂_hR = 2ε²Σ_zu_3(0,0,z) + ∂_h(u_3(0,0,0)/m) is ε-uniform and finite in φ⁴₂ (tree level: u_3 ≈ −24λm∫G³).
- The first term is ≤0 by GHS (Ellis–Monroe–Newman, valid for φ⁴).
- Random-current form via (I2) at y=0: R = 2⟨φ_0²⟩·P^{2δ_0,δ_0+δ_g}[loop at 0 ↮ path 0→g]. Here ⟨φ_0²⟩ is ↑ in h (GKS) and the disconnection probability is "morally" ↓. Random-current measures have no FKG, which is the whole difficulty.

**Sanity checks.**
- Gaussian: R ≡ 2σ², so ∂_hR = 0; (★★) holds with equality at C=8.
- Weak coupling in any d: h/m = μ + 4λ(m² + 3(G−c)) + O(λ²) gives m−hχ = 8λm³χ = 8λm²|∂_μm| + O(λ²). So **C=8 is saturated at first order**, and the inequality is decided by the sign at second order.
- Numerics (scratch quadrature, λ=1, ratio (m−hχ)/(λm²|∂_μm|)):
  - single site, μ ∈ [−400, 10³], h ∈ [10⁻², 5·10³]: sup ≈ 7.9999 → 8⁻ (approached at weak coupling and at large h);
  - 2-site ring (J ≤ 10): max 7.968;
  - 3-site ring: max 7.927.
  - One single-site point at μ=10³, h=10⁻² read 10.38. This is floating-point error: there m ≈ 10⁻⁵ and m−hχ ≈ 10⁻¹⁷.

  So R is nonincreasing in every case tested.
- Mean-field Landau: C=8 exactly.

## 4. Assembly — PROVED conditional on (★★)

Given (★★) with an ε-uniform C:
- m is ↑ in h and ↓ in μ (GKS).
- The ABF / Aizenman–Barsky integration (as in [1]) then turns m ≤ h∂_hm + Cλm²(−∂_μm) into m(μ,0+)² ≥ (μ_c−μ)/(C′λ) for μ<μ_c. This is dimensionally correct and uniform in ε.
- No o(1) errors are needed: (★) is exact at every ε. The only limit-sensitive input is the finiteness of ∂_h of Wick-ordered same-site quantities, which is standard for φ⁴₂.
- Optionally an m³ term can be added (it is dimensionless in d=2, and it is ABF's M³). The numerics suggest it is unnecessary.

## 5. Where the genuine new idea is needed

Not in the λ-prefactor: (★) settles that exactly, and it vindicates the reviewer's dimensional claim. The gap is entirely in

**Target lemma (same-site ratio monotonicity).** For nearest-neighbour lattice φ⁴ (any d, ε, a∈ℝ, b>0, plus state, h>0):
∂_h[⟨φ_0;φ_0²⟩/⟨φ_0⟩] ≤ K·∂_h⟨φ_0²⟩, with K independent of ε (conjecturally K=0).

Equivalently, using GHS for the first piece, it suffices that **∂_h(u_3(0,0,0)/m) ≤ 2ε²Σ_z|u_3(0,0,z)| + K∂_h⟨φ_0²⟩.**

Suggested attacks, in order:
- (a) Prove it in 0-d and for finite GS blocks, where the numerics say K=0 works. Look for a Lee–Yang / GHS-type proof: R(h) is a ratio of cumulants of a Lee–Yang measure.
- (b) Lift it to the lattice via the tangled-current form of R and a ghost-derivative identity for P^{2δ_0,δ_0+δ_g}[↮]. The h-derivative opens one extra ghost edge, and one needs that the extra strand reconnects the loop to the path with probability ≥ the Gaussian 2/3-pairing value. **This "tangling at least as strong as Wick" comparison is the precise new input.**
- (c) Alternatively, use the BFS random-walk representation (Brydges–Fröhlich–Sokal, CMP 91 (1983)), whose skeleton inequalities already carry the true λ, uniformly in ε for d<4.

## Sources
1. M. Aizenman, D. Barsky, R. Fernández, J. Stat. Phys. 47 (1987) 343. Background for the decomposition: H. Duminil-Copin, lecture notes, https://arxiv.org/abs/1707.00520.
2. M. Aizenman, H. Duminil-Copin, Annals 194 (2021): https://arxiv.org/pdf/1912.07973 (GS blocks eqs. 2.1–2.4; switching Lemma 3.3).
3. T. Gunaratnam, C. Panagiotis, R. Panis, F. Severo, https://www.arxiv.org/pdf/2211.00319 (weights eq. 3.2; Remark 3.3 says the classical switching proof fails for φ⁴ weights; tangled currents Def. 3.14; switching Thm 3.12, Cor 3.15, Prop 3.17; derivatives Prop 3.20; Wick limit Rem. 3.16).
