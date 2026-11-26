# Fable session notes — (P)/(P0) for lattice φ⁴₂ (26 Nov 2026)

**Verdict.** (P) and (P0) are NOT proved. No reason was found that either fails. What exists now:
- an unconditional, ε-uniform inequality that is (P0) with K = 24λ up to an explicit additive defect (PROOF.md Thm 1), vacuous in the flip regime;
- a derivative-free, convexity-free form of the open input, (FD_κ), proved to imply the integrated (P0) (PROOF.md Thm 4), proved on one site (Thm 2), and tested numerically in Curie–Weiss, 1D rings and 2D tori;
- a list of dead routes (FAILED.md).
Labels: PROVED / CN (checked numerically) / HEUR / CNR (cited, not read).

Read: paper/body.tex (all), vehl/NOTES.md, r2/{A,B,C,D}/NOTES.md, r2/E/RESULTS.md, theta2/NOTES.md, theta3/NOTES.md, mc/RESULTS.md, lift/SWITCHING.md (first half). Not read: theta1/PROOF.md, zerod/*, lift/A.md, lift/CONVEX.md.
Notation as in PROOF.md §0 (lattice units; Y = M/N; m_k = ⟨Y^k⟩; τ = m4/(3m2); c = 2a − 4).

## 1. Exact identities at zero field (all PROVED by IBP algebra; CN where stated)

(1.1) |B_L| = 12b[(−∂_a m2) + R″(0)/N], i.e. |B_L| = 24λ(−∂_μM_L²) + 12λ ∂_h²R(0)/L².
 - From the paper's identity (4.1) expanded to order h³. So (P0) ⟺ R″(0) ≤ K′·(−∂_aχ): Lemma L at second order in h.
 - CN: scripts/verify_ring.py, rings N = 4, 6, 8, agreement 5 digits; R″(0)/(−∂_aχ) = −0.57, −0.50, −0.73 (N = 4, 6, 8).
(1.2) ⟨φ0²⟩ + R(0) = (1/χ − c)/(4b) (h-derivative of the EOM at 0).
(1.3) Zero-mode transport equation. With I_N(y) = −N⁻¹log p(y) (p = density of Y), σ(y) = E[Φ2 | Y = y], R_mc(y) := E[Σ_xφ_x²(φ_x − y) | Y = y]/(Ny):
   I_N′(y)/y = c + 4b[σ(y)/N + R_mc(y)],  ∂_aI_N = σ/N − ⟨φ0²⟩,
   hence in w = y²:  ∂_aI_N − (2b)⁻¹∂_wI_N = −R_mc(w) + const(a).
 - If R_mc were constant the law of Y² would be transported rigidly at the Landau speed −1/(2b) (continuum: dM²/dμ = −1/(4λ)).
 - This is theta3 (1b)+(1c) combined; the transport reading is new here.
 - R_mc(y) = 2v(y) + k(y)/y with v = E[ψ0² | y], k = E[ψ0³ | y], ψ = φ − Y; also N y R_mc = (2N)⁻¹Σ_{x,x′}E[(φ_x − φ_{x′})²(φ_x + φ_{x′}) | y] (pairs of sites play the role of the two copies in the one-site theorem).
(1.4) Moment-ratio form. With E_k the y^k-size-biased law of Y:
   −∂_a log(m4/m2) = |B| m2/(4b m4) − N(E_4 − E_2)[R_mc],  and  −∂_a m2 = Λ/(4b) − N Cov(Y², R_mc),
   Λ := Cov_p(y², U′(y)/y), U = −log p; Λ = 1 + 2m2∫_0^∞(p(y) − p(0))y⁻²dy.
 - Sufficient pointwise condition for −∂_a(m4/m2) ≥ δ|B|/(4b): (1−δ)y² + (1−3δ)v(y) − δk(y)/y nondecreasing in |y|. At δ = 1/3 only the conditional skewness enters: 2y² − k(y)/y nondecreasing.
 - These are reformulations. They do not help unless a canonical (fixed-Y) monotonicity can be proved, and the pointwise ones fail for weakly coupled deep wells (FAILED.md F5).
(1.5) O(2) check (HEUR): for a two-component field R_mc contains E[ψ¹(ψ²)² | y]/y ≈ −E(ψ²)⁴/(2y²), strongly increasing in y. So the one-component input sits in "R_mc does not increase".

## 2. The Bogoliubov-type inequality (PROOF.md Thm 1; PROVED, CN)

24λ(−∂_μM_L²) ≥ 2|B_L|/(2 − |B_L|) − (χ_L m_H² − 1), χ_L m_H² − 1 = 4λε²Σ_x|u4(0,0,0,x)|.
- Test function: G0 = Y·Σ_x∂_xS (generator of dilation of the zero mode). One-site case gives monotonicity of the Binder cumulant in the mass and the one-site finite-difference inequality (Thm 2).
- Why it cannot be improved to (P0) inside this method (HEUR): in a pure phase the correlation of G0 with Y² is 1/(χ₊ m_H²), which is 1 only when the Hartree mass is exact. Any test function of the form f(Y)Σ∂_xS − f′(Y) has the same defect. Removing it needs test vector fields that involve the non-zero modes, i.e. the solution of the Helffer–Sjöstrand equation.
- A 3×3 Gram version with (Y², Φ2, G0) gives Cov(Y², Φ2) ≥ [ab − √((AV−a²)(BV−b²))]/V (a = 2m2, b = 2Nm2, A = Var Y², B = Var Φ2, V = Var G0). In mean field both deficits vanish and this is the Landau bound −∂_aM² ≥ 4M²/m_H²; in general it needs upper bounds on Var(Y²) and Var(Φ2) (HEUR; not pursued).
- Respects (O3): nothing one-component is used, and the result is correspondingly weak.

## 3. The finite-difference form (PROOF.md Thms 3, 4)

(FD_κ): ⟨M⁴⟩_μ ≥ 3⟨M²⟩_μ · ⟨M²⟩_{μ + 8κλM_L²(μ)}, i.e. M_L²(μ + 8κλM_L²(μ)) ≤ (1 − |B_L(μ)|/3)·M_L²(μ).
- PROVED: (FD_κ) on a window ⟹ M_L²(μ₋) ≥ (48κλ)⁻¹∫_W|B_L|dμ (telescoping; no derivative, no convexity; avoids (O5)).
- PROVED: (FD_κ) ⟺ E_ŵ[X(a + 4bt_ω)] ≥ X(a + 4bκm2) (BFS chain, Thm 3): one two-point walk's local time, as a mass increase, lowers the susceptibility no more than the uniform increase κ·4b·m2. Since E_ŵ|t|/N ≤ m2, this is implied by the deterministic comparison
  (UNI_κ) X(a + s) ≥ X(a + κ·mean(s)) for the mass fields s = 4bt occurring under ŵ
  together with a Markov step (which costs constants: with (UNI_κ) for all s ≥ 0 one gets M_L²(μ) ≥ B0²(μ′ − μ)/(288κλ) whenever |B_L| ≥ B0 on [μ, μ′]; PROVED, see §3.1).
- Gaussian case: (UNI_1) holds for every s ≥ 0 by ⟨1,(A+s)⁻¹1⟩ ≥ N²/⟨1,(A+s)1⟩ (PROVED).
- CN, rings N = 8 (scripts/uni_test.py, 45 cases, half/alternating/single-site s, amplitudes up to 8×): (UNI_1) held in every case.
- HEUR (Landau, tree level): in an ordered phase (UNI_1) fails for modulations of wavelength ≳ correlation length (M is concave in μ); with local equilibrium κ ≥ 1/(2β) suffices. So (UNI_κ) is again a "no plateau" statement.
- HEUR: for 2D O(2) in the KT phase a Dirichlet line has mean(s) ~ 1/L and lowers X by a constant factor, so (UNI_κ) fails; at a 2D Ising critical point the same defect is marginal (ν = 1). (UNI_κ) encodes "mass is a relevant perturbation with ν ≤ 1".
- CN for (FD_κ), minimal κ (scripts fd_1site.py, fd_cw.py, fd_ring.py; mc2d/):
  - one site: κ_min ∈ [0.30, 1.00), → 1 as a → +∞ (Gaussian), → 1/3 for deep wells. PROVED κ = 1.
  - Curie–Weiss, N = 64…16384, b = 1…0.005: κ_min ∈ [0.18, 0.995].
  - rings, N = 4, 16, 64, b = 0.5, 0.1, 0.02 (72 cases): κ_min ∈ [0.13, 0.83].
  - 2D tori L = 16, 32, b = 0.5, 0.1, 0.02, 26 masses each (Monte Carlo with the validated mc/phi4 code, 6·10⁴–10⁵ sweeps, log-linear interpolation of m2 in a, jackknife): for |B| ≥ 0.1 the largest κ_min is 1.00 ± 0.11; in the critical and ordered regions κ_min = 0.08–0.35 and decreases with L. For |B| < 0.1 (deep disordered) unresolved (errors ≥ 0.3; one point 4.7 ± 1.6 at |B| = 0.04).
  - In all exact tests the stronger self-consistent form m2(a + 4bτ) ≤ τ also held.
- At first order in b, κ = 1 is exact (κ_min = 1 + R″(0)/(−∂_aχ)); κ ≤ 1 there is Lemma L at second order.

### 3.1 Markov step (PROVED)
If X(a + s) ≥ X(a + κ mean(s)) for all s ≥ 0, then by (3.1), (3.3) and Markov (P_ŵ(|t|/N ≥ θm2) ≤ 1/θ), for θ = 6/|B|:
f(a + 24κb f(a)/|B(a)|) ≤ (1 − |B|/3)/(1 − |B|/6)·f(a) ≤ (1 − |B|/6) f(a).
Iterating on a window where |B| ≥ B0: the masses a_k converge within distance 144κb f(a)/B0², while f(a_k) → 0, impossible on a finite torus. Hence |B| ≥ B0 on [a, a+Δ] forces f(a) ≥ B0²Δ/(144κb).

## 4. Other things tried
- Rigorous lower bound on E_ŵX from Bogoliubov + Jensen (PROVED, CN one site): 1 − |B_L|/3 ≥ 1/(χ_Lm_H² + 8λχ_L²/L²). First-order exact, vacuous for χ²/L² large.
- "Lemma L ⟺ F_w ≤ 4λF_μ" for F(μ, w) = h/m at m² = w (PROVED algebra): h/m is nonincreasing along μ + 4λm² = const. Equivalent well-picture: for the weight e^{−λ(φ²−w)²−κφ²/2+hφ}, with h tuned so that ⟨φ⟩² = w, h/√w is nonincreasing in w. No proof found.
- Lee–Yang form of the m4/m2 inequality: no sign structure found.

## 5. Single most promising step
Prove (FD_κ) (any fixed κ) on the torus, i.e. ⟨M⁴⟩_μ ≥ 3⟨M²⟩_μ⟨M²⟩_{μ+8κλM_L²}. It is a correlation inequality between the same model at two masses, with no field and no derivative. Routes:
(a) a walk/loop "switching" argument for E_ŵ[X(a+4bt)] ≥ X(a + 4bκm2) that uses one-componentness (it must fail for O(2));
(b) (P0) for one K plus monotonicity of B_L in μ gives (FD) by the Riccati-type integration used in Thm 2(c) — so on the lattice the missing piece is exactly the Hartree defect of Thm 1.
Non-Gaussianity of the torus magnetisation remains open and untouched.

## 6. Files
scripts/: cw.py, fd_cw.py, fd_1site.py, ring.py, fd_ring.py, verify.py, verify_ring.py, verify_Z.py, uni_test.py, lam.py. mc2d/: run.py, ana.py, res_*.json, ANALYSIS.txt.
