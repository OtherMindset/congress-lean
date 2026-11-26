# vEHL double cluster swapping (arXiv:2609.01362) vs inequality (P): notes, 26 Nov 2026

Verdict: **(c) FAILS.** The new obstruction is (O7), stated in Section 4 below.
Labels used: PROVED, CHECKED-NUMERICALLY (CN), HEURISTIC (HEUR), CITED-NOT-READ (CNR), READ-VIA-SUMMARY (RVS).

## 0. What was read
- body.tex, all of it (§§2–9).
- r2/B/NOTES.md and r2/D/NOTES.md.
- arXiv:2609.01362v1 (the only version). I could not download it: curl to arxiv.org gets proxy 403. I read it with WebFetch on the HTML version (offsets 0, 60k, 100k of 143k characters). WebFetch returns a model summary, not the original text, so every statement below from vEHL is **RVS**. I did not see the text of Definition 3 (class E), Assumption 2, eq. (6), eq. (11) (Φ) or the proof of Lemma 22. Statements I relied on:
  - Def. 1 (model): ⟨F⟩ ∝ ∫F exp(β Σ J_uv φ_uφ_v + h Σφ_u) Π dλ(φ_u), with λ even and super-Gaussian (Assumption 1).
  - Def. 4 (representation): φ^± = (φ ± φ')/2 and ξ^± = |φ^±|. ω^+ on E ∪ ghost edges: an edge opens only if φ^+_uφ^+_v > 0, then with prob. 1 − e^{−4βJξ^+_uξ^+_v}; ghost edges open with prob. 1 − e^{−4hξ^+_u}. ω^− on E is defined the same way, without ghost edges.
  - Prop. 5 (swapping): given (ξ^±, ω^±), the signs of φ^± can be flipped on any ω^± cluster except the ghost cluster.
  - Prop. 6: (ξ^+, −ξ^−, ω^+, −ω^−) is FKG, so ω^+ and ω^− are negatively associated.
  - Identities (13)–(16).
  - Thm 3 (sharpness for P ∈ E): χ < ∞ for β < β_c, and ⟨φ_o⟩^+_β ≥ c(β − β_c)/β (eq. (7)/(56)).
  - Prop. 16 (Simon–Lieb) and Lemma 17 (φ_β(S) < 1 ⇒ χ < ∞).
  - Prop. 20 and its finite-volume form (51), Steps 1–4.
  - Lemma 21 (⟨|φ_o|⟩ ≤ C(ε′, P, Γ) for β ≤ 1/ε′, h ≤ 1), Lemma 22 (E[|φ^+_v| | 𝒮 = S] ≥ c(ε′)), Lemma 23, and the bound (61)–(62) via F(α, γ).
  - Caveat (RVS): the summary defines 𝒮 = {v ↔ ghost in ω^+}, but then writes "1(o ∈ 𝒮)" and "o ↔ u inside 𝒮". Step 4 only makes sense if 𝒮 is the **complement** of the ghost cluster, so I read it that way. The argument below does not depend on this choice.

## 1. Their key inequality, exactly as reported (RVS)
- Derivative: in **β**, with P, J and h fixed: d⟨φ_o⟩/dβ = ½ Σ_{u,v} J_uv ⟨φ_o; φ_uφ_v⟩.
- Representation of the bond term: ⟨φ_o; φ_uφ_v⟩ = 2E[ξ^−_o ξ^−_u ξ^+_v 1(o ↔^− u) 1(v ↔^+ g)] + (u ↔ v). (I derived this independently: PROVED from Prop. 5 and CN, §3.)
- Prop. 20 / (51) (DCT-type rather than ABF-type):
  dm/dβ ≥ (c/β) · inf_{S∋o} φ_β(S) · (1 − 2m/⟨|φ_o|⟩) − ε_β(G_n, h),
  with φ_β(S) = β Σ_{u∈S, v∉S} J_uv ⟨φ_oφ_u⟩_{S,β,0}.
- Constants:
  - c = c(ε′, Γ, P) comes from Lemma 22. It is a uniform lower bound on the conditional mean of |φ^+_v| off the ghost-free region, obtained via inf F(α, γ) over α ≤ 3C′ and γ ≤ 6C/ε′.
  - C = C(ε′, P, Γ) comes from Lemma 21.
  - The error term ε_β is a box-boundary term that vanishes as n → ∞ by GHS.
- Integration: for β ≥ β̃_c the factor inf φ_β ≥ 1, which gives m ≥ (c/2)(β − β̃_c)/β ∧ C/4. Every constant is for a **fixed** single-site measure and graph. No constant is given explicitly.

## 2. The inequality in our variables

**PROVED (scaling identity).** With φ = ψ/√β, m(β, a, b, H) = β^{−1/2} m(1, a/β, b/β², H/√β). At β = 1:

  β∂_β m = −a∂_a m − 2b∂_b m − ½m − ½H∂_H m.

In continuum units (a = 2 + ε²μ_b/2, b = λε², μ_b = μ − 12λc_ε, H = ε²h) this becomes

  β∂_β m = (4ε^{−2} + μ + 12λc_ε)(−∂_μ m) − 2λ∂_λ|_μ m − ½(m + hχ).   (2.1)

This is (O1) made exact.

So Prop. 20 at β = 1 says, in our variables:

  −∂_μ m ≥ (ε²/4)(1 + O(ε² log ε^{−1})) · [ c · inf_S φ_1(S) · (1 − 2m/⟨|φ_0|⟩) + ½(m + hχ) + 2λ∂_λ m ] − (boundary error).   (2.2)

The integrated form (7) behaves the same way. Raising β by δ at fixed P is the same as lowering μ_b by 4δ/ε², up to O(δ) relative changes of b and H. So β̃_c(P_μ) = 1 − ε²(μ_c − μ)/4 + o(ε²), and (7) gives **M^+ ≥ (c/4)ε²(μ_c − μ)(1 + o(1)) → 0** (HEUR for the o(1); the scaling itself is PROVED).

Our (P) with θ = 1 needs −∂_μ m ≥ (1 − hχ/m)/C with C uniform, i.e. an O(1) lower bound. To get that from (2.2) one would need c · inf_S φ_1(S) ≳ ε^{−2}. This is false:
- **inf_S φ_1(S) ≤ φ_1({o}) = 4⟨φ²⟩_{one site, a, b} = 1 + O(ε² log ε^{−1})** (CN, `scripts/checks.py` part 1: (φ − 1)/(ε² log ε^{−1}) → 0.37 at λ = 1, μ = 0, for ε = 2^{−3} to 2^{−10}).
- **PROVED, massless Gaussian (a = 2, b = 0):** φ_1(S) ≡ 1 for every finite S. The free-boundary covariance on S is (4I − A_S)^{−1} = ¼G_S^{SRW}, so φ_1(S) = Σ_u G_S(o, u) · #exits(u) / 4 = P_o(SRW exits S) = 1. In other words, φ_β(S) is **normalised by harmonic measure**: it counts one first-pivotal layer of bonds whose total weight is O(1).
- **PROVED: c ≤ 2E|φ^+_v| ≤ √(2(⟨φ²⟩ + m²))**, whenever P(v ∉ ghost cluster) ≥ ½ (Lemma 22 is a uniform lower bound on a conditional mean, so it is at most the unconditional mean divided by P(v ∉ 𝒮)). With ⟨φ²⟩ = c_ε + O(1) (standard Wick estimate; HEUR here) this gives c ≲ √(log ε^{−1}/π). As ε → 0, Lemma 21/22 may make c *smaller* still: C(ε′, P_ε) ~ ε^{−1} if 1/ε′ is fixed above 1, because |φ| ~ (λε²)^{−1/2} at β = 1/ε′ > 1 (HEUR; I did not see the proof of Lemma 22).
- Hence the right side of (2.2) is O(ε² √(log ε^{−1})). **The loss is ε^{−2}/√(log ε^{−1}), for every λ.**
- Could E[1(o ∉ ghost) φ(𝒮)] beat inf φ? HEUR: in the continuum, φ(S) is a boundary flux ∫_∂S ∂_n⟨φ_oφ_y⟩_S, an O(1) continuum quantity with no power of ε^{−1}. It equals 1 exactly at the Gaussian point.

**Site-parameter derivative (task 2).** I worked out the exact site analogue. PROVED from Prop. 5, by the same computation as the bond identity: ⟨φ_o; φ_z²⟩ = ½E[(φ_o − φ'_o)(φ_z² − φ'_z²)] = 4E[φ^−_o φ^−_z φ^+_z]. Then flip clusters:

  ⟨φ_o; φ_z²⟩ = 4E[ξ^−_o ξ^−_z ξ^+_z 1(o ↔^− z) 1(z ↔^+ g)],   −∂_μ m = 2ε² Σ_z E[⋯].   (S)

CN: agrees with direct enumeration to 10 digits on a 3-site path with two discrete spin laws (`checks.py` part 2). The bond identity (B) agrees too.

The difference from the bond case is structural:
- In (B), the ω^−-requirement (o ↔ u) and the ω^+-requirement (v ↔ ghost) sit at **two adjacent sites**. vEHL can therefore keep the ω^− path inside the ghost-free region and pay only the magnitude |φ^+_v| ≥ c across one bond (Step 1 is FKG in the favourable direction).
- In (S), both requirements sit at the **same site z**, so the ω^− connection has to enter the ghost cluster. By Prop. 6 (ω^+ and ω^− negatively associated) the FKG bound then goes the **wrong way**:
  (S) ≤ 4E[ξ^−ξ^− 1(o ↔^− z)] · E[ξ^+_z 1(z ↔^+ g)] = 2m⟨φ_o; φ_z⟩.
  This is GHS, u3(o, z, z) ≤ 0 (CN: holds at every point in `checks.py`).
- No decoupled lower bound −∂_a m ≥ κ · 2mχ is possible in the flip regime. Curie–Weiss φ⁴ (`scripts/cw_flip.py`, a = 0.6, b = 1, J = 4, N = 64…16384, x = NHM ∈ {0.3, 1}) gives r = (−∂_a m)/(2mχ) ≈ 15/N and 26/N (CN). The mass shift does not flip the torus magnetisation, but χ ~ NM² does.
- Restricting (S) to sites z just outside the ghost-free region gives a harmonic-measure-normalised O(1) lattice sum again, i.e. O(ε²) in continuum units. So the site version fails in both of the ways it could be set up.

**Torus/flip remark (HEUR).** On a torus there is no box error. But when no site connects to the ghost, 𝒮^c is the whole torus and φ = 0. That event has probability bounded below when x = HNM = O(1), which is exactly the flip regime. So even at fixed ε the DCT bound degenerates there, which is consistent with dm/dβ = O(h) as h → 0 on a finite torus.

## 3. Check against our obstructions
- **(O3):** passed in principle. The method uses Prop. 5's real-valued Z2 cluster sign flips and the ghost cluster, and its conclusion (a linear lower bound on M^+) is false for 2D XY. So it is genuinely one-component. (HEUR: I did not locate the step that fails for O(2).)
- **(O1):** the failure is a sharper form of (O1). The loss is ε^{−2} with no λ, not 1/(λε²), because the DCT right-hand side is m-independent and normalised to 1 at the Gaussian point.
- **Prop. 5.3 / (O2):** an ε-uniform version of (2.2), −∂_μ m ≥ κ(1 − 2m/⟨|φ|⟩), would fail for the profile in Prop. 5.3, where −∂_μ m = m/(1 + F) → 0. That is consistent, since that profile is not a spin model. No contradiction with (O5), because (S) is not a convexity statement.
- **On a finite torus**, the uniform form with inf_S φ ≥ 1 would contradict m = O(h) as h → 0. The inf over S then has to include S = Λ, where φ = 0, so the bound is vacuous there.

## 4. Verdict: (c) FAILS, new obstruction (O7)

**(O7) Pivotal-layer bounds lose ε^{−2}.**
- vEHL's Prop. 20 bounds β∂_β m below by c · inf_S φ_β(S) · (1 − 2m/⟨|φ|⟩).
- The quantity φ_β(S) is harmonic-measure-normalised: φ_1(S) ≡ 1 at the massless Gaussian point (PROVED), and φ_1({o}) = 1 + O(ε² log ε^{−1}) on our family (CN). Also c ≲ √(log ε^{−1}) (PROVED from Lemma 22's form plus the Wick estimate).
- By the exact scaling identity (2.1), β∂_β m = (4ε^{−2} + O(log ε^{−1}))(−∂_μ m) + O(1). So in continuum units the bound reads −∂_μ m ≳ ε² √(log ε^{−1}), and (7) gives M^+ ≳ ε²(μ_c − μ). Both are vacuous.
- The loss is in **Step 3 of Prop. 20**. It keeps only the first-pivotal bond layer at the boundary of the ghost-free region, which has O(1) total weight in lattice units. The continuum μ-response, (ε²/2)Σ_z⟨φ_0; φ_z²⟩, is a bulk sum over ~ε^{−2} sites.
- Replacing ∂_β by a site (φ²) derivative is exact via (S), but the two connection events then sit at one site. Negative association (Prop. 6) then gives only the upper bound (GHS). The bulk decoupled lower bound is false by a volume factor in the flip regime (CN, CW), and the boundary version reproduces the ε² loss.

**What a working argument would need** (not a smaller lemma; recorded for orientation): a lower bound on the **bulk** sum in (S) by a pivotal quantity with continuum normalisation. That means a positive-correlation statement between "o ↔^− z" and "z ↔^+ ghost" at the same site, beyond the FKG of Prop. 6, which is false in its naive decoupled form (CW). This is the same screening issue as r2/B §4 (ST_θ), now in cluster language.

Files: `scripts/checks.py` (single-site φ({o}); exact 3-site enumeration of (S), (B) and the decoupling direction), `scripts/cw_flip.py` (Curie–Weiss flip-regime ratio).
