# Member B, round 2: φ⁴-specific representations (26 Nov 2026)

Lattice units throughout: weight exp(Σ_{xy}J_{xy}φ_xφ_y + HΣφ − Σ(aφ²+bφ⁴)), vertex-transitive graph, uniform H ≥ 0.
s = φ²/2, g(σ)=e^{−2aσ−4bσ²}, F(t)=log Z(t), Z(t)=∫e^{...}Π g(s_x+t_x).
S = −∂_a m = Σ_z⟨φ_0;φ_z²⟩. Target (SP): m − Hχ ≤ C b m^θ S.
BFS walk measure: w_0(dω) = dW_0(ω) Z(t_ω)/Z (positive, mass m, dW_0 independent of a,b). T = ∫w_0 |t_ω|.
Key fact used repeatedly: g(σ+r) = const·e^{−(2a+8br)σ−4bσ²}, so an extra local time r_z is
exactly a mass shift a_z → a_z + 4b r_z. Write m_y^{(r)} = ⟨φ_y⟩ in the model with masses a + 4b r.

## 1. GPPS tangled currents (arXiv:2211.00319): read, assessed (abstract + §3/§4/App.B via WebFetch)
- Switching principle Thm 3.12 / Cor 3.15 / Prop 3.17 holds for real-valued φ⁴. The tangling measure ρ is a
  weak SUBSEQUENTIAL LIMIT of Griffiths–Simon block-spin double-current pushforwards; it depends only on
  (Δn₁(z), Δn₂(z), A_z, B_z). Only qualitative facts are proved (Prop 4.1: ρ(P) ≥ κ(M) > 0). There is no ABF-type
  inequality in the paper, and no quantitative b-dependence. The derivative formulas (Prop 3.20) are the
  standard ∂_β, ∂_a, ∂_g ones.
- For (SP) one would need P(a class of size ≥ 4 merges two currents at z) ≤ C·b·(degrees), uniformly. This is not
  available, and GS blocks cannot supply it: they produce φ⁴ only through near-critical Curie–Weiss blocks.
  Counting intra-block pivotal bonds gives K∂_K ~ N^{1/2}(−∂_a), which is worse. HEUR.
- Structural diagnosis: an ε-uniform (SP) needs (i) exact cancellation of the Gaussian part, so that the prefactor is b,
  AND (ii) a screened (truncated) pivotal quantity. Random walks do (i) but not (ii). ABF/currents do (ii) (the
  "first pivotal" plus conditioning-reversal produces ⟨σ0;σuσv⟩) but not (i). The construction below does both
  at the level of identities.

## 2. New exact identities (PROVED from BFS + translation invariance; checked numerically)
(W1)  H T = ∫ w_0(dω) m_0^{(t_ω)}.
  Proof: split the walk at its local time at z: τ_0(z) = ∫∫dW_{0z}dW_z Z(t₁+t₂)/Z = ∫w_z(dω₂) A^{(t₂)}_{0z}.
  Sum over z, translate ω₂ to start at 0, use A_{y0}=A_{0y} and Σ_y A^{(r)}_{0y} = m_0^{(r)}/H (any environment).
(W2)  **H T ≤ m².** Since m_0^{(r)} ≤ m for r ≥ 0 (GKS/Ginibre: −∂_{a_z}⟨φ_0⟩ ≥ 0). Gaussian case: equality up to Hχ ≤ m.
(W3)  m − Hχ = H ∫ w_0(dω) Σ_y [ m − m_y^{(t_ω)} ]   (RW0 rewritten).
  In words: the total magnetisation lost when the masses are raised by 4b × (a field-walk's local time).
  This gives m ≥ Hχ from GKS alone.
(W4)  Mean-value form: m − Hχ = 4bH Σ_x ∫w_x(dω)∫_0^1dv ⟨t_ω, S^{(v t_ω)}⟩, with all terms ≥ 0.
  Its tangent part is exactly 4b(HT)S. The remainder is
  E3 = −16b²H∫w_0∫_0^1(1−v)Σ_{zw}t_zt_w⟨M;φ_z²;φ_w²⟩_{(a+4bvt)}dv.
(W5)  Hence, EXACTLY,  m − Hχ = 4 K_eff b (HT) S ≤ 4 K_eff b m² S, where
  K_eff := E_{w0}[ΔM_tot(4bt)] / E_{w0}[⟨4bt, −∇_a M_tot⟩]
  is the SECANT/TANGENT ratio of M_tot(a) = Σ_y m_y along walk-shaped mass increases.
Consequences:
- **(SP) ⟸ K_eff ≤ C m^{θ−2}** on the flip region.
- **Lemma L (K=0) ⟸ K_eff·(HT/m²) ≤ 2.**
- K_eff ≤ 1 if M_tot is convex in the masses along positive directions, i.e. the third cumulant ⟨M;φ²;φ²⟩ ≥ 0.

Numerics:
- one site, screened1site.py: h⟨⟨B⟩⟩ = 4bhTS + E3 to 5e-3. K_eff = 0.96, 0.75, 0.63, 0.59. hT/m² = 0.98, 0.81, 0.63, 0.52.
- 2-site transitive graph, exact walk sums, rw2site.py: (W1) and (W3) hold to grid error (0.2–0.4% at the finest grid).
  HT/m² = 0.58–0.96, K_eff = 0.59–0.94.

## 3. Screening is resonant in the ordered phase (PROVED algebra + NUM)
- ∇²F(t) = −8b I + 64b² Cov_t(s,s). On the zero mode the effective local-time vertex is 8b(1 − 2bχ₂), with
  2bχ₂ = 2b(−∂_a⟨φ²⟩) = 4λ(−∂_μ⟨:φ²:⟩).
- Mean field in the ordered phase: −∂_a M² = 1/(2b), so 2bχ₂ = 1 + fluctuations. log Z(t) is exactly AFFINE in uniform t
  until the order melts (computed: f(τ)/N = −Jτ for τ ≤ τ* = M²/2).
- NUM, Curie–Weiss (cw_plateau.py, a=1.9, b=0.02, J=4): 2bχ₂ = 1.02–1.12 > 1 for N = 64–1024.
- Near μ_c, χ₂ ~ the specific heat, which diverges logarithmically in 2D, so screening is O(1) on both sides.
- This is why every Taylor expansion in b around free walks loses. It also explains RW1's volume loss: in the flip regime
  B₁₂ = 4bN(σ−τ*)²₊ ~ λ|T| on pairs whose combined local time melts the order, so 1−e^{−B} ≤ B loses |T|.
  (W3)/(W5) avoid this: no linearisation, and the indicator-like saturation is kept inside ΔM.
- MF picture of the flip regime (HEUR): m − Hχ counts PAIRS of walks whose combined local time melts the order. S counts
  single walks overshooting the threshold. This is consistent with HT ≈ m²/4 and K_eff ≈ 1.

## 4. Remaining obstruction, precisely
(ST_θ) a uniform secant/tangent ("no-plateau") bound for the response of M_tot to walk-shaped mass increases:
  E_{w0}[M_tot(a) − M_tot(a+4bt)] ≤ C m^{θ−2} E_{w0}[⟨4bt, −∇_aM_tot(a)⟩].
- Uniform-shift proxy in CW (cw_plateau.log): K_unif = 1.00–1.05 at x ≤ 0.3 and ≤ 1.7 at x = 3, N-uniform.
  No plateau. (Pure-phase MF limit: K = 2, from M ∝ √(a_c−a); a power law m ∝ (a_c−a)^β gives K ~ 1/β.)
- (W1)–(W5) use only BFS walks + GKS mass monotonicity, which hold for O(n) models too. So by member A's XY
  counterexample, **K_eff must blow up for 2D XY**, and the ONE-COMPONENT input must enter exactly in (ST_θ).
  Plausible mechanism: for XY a mass bump is absorbed by spin-wave/vortex softening (a plateau, then a drop).
  This is a target for a switching argument: a sign/size bound on the third cumulant ⟨M;φ_z²;φ_w²⟩ (Ising-specific),
  integrated against local times.
- Trivial bounds on K_eff need a lower bound on S, which is circular.

Files: screened1site.py, rw2site.py, cw_plateau.py, cw_plateau_1.9.log, dl/ (downloads failed: proxy 403).
