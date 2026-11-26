# FAILED.md — routes to NG that do not work (26 Nov 2026)

F1. BFS upper skeleton bound (CNR, CMP 91 (1.4)). It is perturbative in λ·Bub_L. PROVED (PROOF B.4): any bound
    |B_L| ≥ 24g0(1 − CλBub_L) caps at 6/C, because λBub_L ≥ g0 = λχ_L²/L². In W one expects λBub_L → ∞ (HEUR),
    so the bound certifies nothing. It is the weak-coupling case of (NS).

F2. Aizenman–Graham, tree bound, Glimm–Jaffe g_R ≤ const, and Fable's Bogoliubov inequality (fable Thm 1). All give
    upper bounds on |B| (or on |u4|). Wrong direction.

F3. Lee–Yang plus growth order < 2 (PROOF C). This gives B < 0 strictly at each L, and the exact identity
    B = −3Σw_j². It cannot be made uniform. In the rescaled zero mode M/√κ2 the |h|^{4/3} regime moves to
    infinity, so a limit of Lee–Yang functions may be Gaussian (the e^{bh²} factor is allowed in limits).
    Extensive bounds log Z ≤ CL²(1 + |h|^{4/3}) with Jensen's formula give only w_1 ≳ L^{−2}, i.e. |B| ≳ L^{−4}.

F4. Monotonicity of B_L in μ (one site PROVED; torus CN). It transfers lower bounds only to smaller μ. The deep-ordered
    regime (GJS, where order is known) lies below the window and does not reach μ_+ (PROOF D.2–D.3).

F5. One-site / zero-mode effective potential. A one-site lower bound |B| ≥ F(b m2²) needs the zero mode to have a
    quartic-type effective potential of strength ≳ λL². That is the same as NS. GHS for the law of M (concave m(h))
    is satisfied by Gaussians, so it gives nothing.

F6. The exact identity |B_L| = 24λ(−∂_μM_L²) + 12λR″(0)/L² (fable NOTES (1.1)). Integrated over W, NG becomes
    "M_L² drops by O(1) across W, up to the R″ term". Lower bounds on the drop need order (M_L² ≥ c at μ_−),
    so the route is circular.

F7. Fixed-L compactness. At fixed physical L everything is a strictly non-Gaussian continuum measure, but
    no RG-type inequality comparing B_{2L} with B_L is known. A naive criterion "|B_L| ≥ g* ⇒ |B_{2L}| ≥ g*" is false
    for μ > μ_c, where |B_L| decreases through every g* < |B*|. It would need an extra input that excludes the
    disordered phase. Simon–Lieb ≥ 1 is not enough, since the massless Gaussian satisfies it.

F8. Planar random-current argument at fixed ε via the Griffiths–Simon construction. It is not planar at the GS level,
    and connection inside a block when two currents meet at a site has probability O(b) = O(λε²). It is
    non-uniform in ε, so uniformity needs the continuum version (NOTES §5 (b)).

F9. "Sign inequalities only". Every inequality listed in NOTES §0 holds for the λ = 0 Gaussian family with
    covariance (−Δ + L^{−2})^{−1}, which has χ_L → ∞ and B ≡ 0. Any proof has to use the contact term 8b t·t′
    quantitatively at the torus scale.
