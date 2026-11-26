# PROOF.md — (FD_kappa) in the tree-level (bubble) regime, uniform in eps and L  (26 Nov 2026)

Labels: PROVED (full argument here) / CN (checked numerically, script named) / CITED (standard theorem, statement used as given; not re-read this session).

## 0. Setting
Finite vertex-transitive graph Lambda with N sites and ferromagnetic nearest-neighbour coupling 1 (the 2D torus eps Z^2 / L Z^2 is the case of interest). Weight
  exp( sum_<xy> phi_x phi_y - sum_x (a phi_x^2 + b phi_x^4) ),  b > 0,  zero field.
G(x,y) = <phi_x phi_y>, chi = sum_y G(0,y), M = sum phi_x, X = <M^2> = N chi, m2 = <(M/N)^2> = chi/N,
B = <M^4>/X^2 - 3 (Binder), u4 = fully truncated 4-point function, B2 := sum_z G(0,z)^2 (bubble).
Quantities at uniform mass u are written chi(u), B2(u), etc.

(FD_kappa) at a:   m2(a + 4 b kappa m2(a)) <= (1 - |B(a)|/3) m2(a).
(FD_kappa) => (FD_kappa') for kappa' >= kappa, since m2 is nonincreasing in the mass.
Continuum dictionary (b = lambda eps^2, d_a = 2 eps^-2 d_mu, Riemann sums eps^2 sum -> integral):
  theta := 12 b B2 = 12 lambda \int_{T_L} G(0,z)^2 dz,    x := b chi^2/N = lambda chi_L^2 / L^2 = lambda L^2 M_L^4,
  and (FD_kappa) reads M_L^2(mu + 8 kappa lambda M_L^2(mu)) <= (1 - |B_L|/3) M_L^2(mu).

## 1. Inputs
(I1) Skeleton (tree) inequality [BFS82; FFS92 ch. 12 — CITED]. For all x1..x4:
     u4(x1,x2,x3,x4) >= -24 b sum_w prod_{i=1}^4 G(x_i, w).
  Derivation from the BFS random-walk representation (the same representation Fable's Thm 3 uses, checked there to 8-12 digits):
  u4 = -sum_{3 pairings} \int\int dW_{12} dW_{34} [Z(t1)Z(t2) - Z Z(t1+t2)]/Z^2; the factorisation Z Z(t1+t2) >= e^{-8b t1.t2} Z(t1) Z(t2)
  (g(s+t1+t2)g(s) = g(s+t1)g(s+t2)e^{-8b t1 t2} plus FKG for the |phi|-marginal, which is MTP2 by GKS II); 1 - e^{-u} <= u; and the
  split identity plus GKS mass monotonicity, \int dW_{xy} (Z(t)/Z) t_w <= G(x,w) G(w,y). The constant 24b is the exact first-order
  coefficient (4! b).  CN: summed forms (S1), (S2) below, rings N = 4,16,64, b = 0.5..0.005 (scripts/thmA_test.py): ratio -> 1 as b -> 0, never violated.
(I2) GKS/Ginibre [Gin70, EMN76 — CITED]: G(0,z) >= 0 and G(0,z) is nonincreasing in the (uniform) mass. Hence B2(u) <= B2(a) for u >= a.
  CN: scripts/ir_check.py.
(I3) (Corollary only) Infrared bound / Gaussian domination [FSS76 — CITED]; needs reflection positivity: nearest-neighbour torus with even side L/eps.
  For k != 0 in the Brillouin zone, Ghat(k) := sum_z G(0,z) e^{ikz} <= 1/E(k), E(k) = 2 sum_i (1 - cos k_i).  Also Ghat(k) <= chi (ferromagnet).
  CN on even rings: max Ghat(k)E(k) = 0.945 <= 1.

## 2. Two consequences of (I1)  (PROVED from I1)
(S1)  |B| <= 24 b chi^2 / N = 24 x.
  Proof: 3X^2 - <M^4> = -sum_{x1..x4} u4 <= 24 b sum_w (sum_x G(x,w))^4 = 24 b N chi^4; divide by X^2 = N^2 chi^2. (The sign B <= 0 is Lebowitz; not needed.)
(S2)  -d_a chi >= 2 chi^2 (1 - 12 b B2).
  Proof: -d_a chi = sum_{x,z} <phi_0 phi_x ; phi_z^2> = sum_{x,z} [u4(0,x,z,z) + 2 G(0,z) G(x,z)] (zero field, odd moments vanish)
  >= 2 chi^2 - 24 b sum_{x,z,w} G(0,w) G(x,w) G(z,w)^2 = 2 chi^2 - 24 b chi^2 B2.
(S3)  theta >= 12 x  (Cauchy–Schwarz: B2 >= (sum_z G(0,z))^2 / N = chi^2/N).

## 3. Theorem A (FD in the bubble regime). PROVED (given I1, I2); CN (scripts/thmA_test.py, 108 ring cases, 0 violations)
If theta = 12 b B2(a) < 1, then (FD_kappa) holds at a for every
   kappa >= kappa_A := 1 / ((1 - theta)(1 - 8x)),   x = b chi(a)^2 / N  (<= theta/12);
in particular for every kappa >= 1/((1 - theta)(1 - 2theta/3)). E.g. (FD_2) holds whenever theta <= 0.34; (FD_3) whenever theta <= 1/2.
kappa_A -> 1 as theta -> 0, matching the first-order saturation of kappa = 1.

Proof. Let delta = 4 b kappa m2(a) = 4 b kappa chi(a)/N. For u in [a, a+delta], by (S2) and (I2),
  -d_u chi(u) >= 2 chi(u)^2 (1 - 12 b B2(u)) >= 2 (1 - theta) chi(u)^2,
so d_u (1/chi) >= 2(1 - theta) and 1/chi(a+delta) >= 1/chi(a) + 2(1-theta) delta. Since delta chi(a) = 4 kappa x,
  m2(a+delta)/m2(a) = chi(a+delta)/chi(a) <= 1/(1 + 8 (1-theta) kappa x).
By (S1), 1 - |B(a)|/3 >= 1 - 8x > 0 (8x <= 2theta/3 < 1 by S3). And 1/(1 + 8(1-theta)kappa x) <= 1 - 8x iff (1-theta) kappa (1-8x) >= 1
(expand: (1+8Kx)(1-8x) >= 1 iff 8x(K(1-8x) - 1) >= 0 with K = (1-theta)kappa). If x = 0 there is nothing to prove. ∎

Remarks.
- Uniformity: theta, x are intrinsic (continuum) quantities: theta = 12 lambda ||G_L||_{L^2(T_L)}^2, x = lambda chi_L^2/L^2. No eps or L enters otherwise.
- Not one-component: (I1), (I2) hold for O(n) phi^4 as well. Consistent with (O3): theta < 1 fails in the KT phase (G not square-integrable uniformly in L) and in every flip regime (theta >= 12x and x = lambda L^2 M_L^4 is large).
- Regime (HEUR, Gaussian approximation G ~ (-Delta + m^2)^{-1}): theta ~ 12 lambda/(4 pi m^2) ~ 0.95 lambda chi, i.e. outside the Ginzburg region lambda chi <~ 1.

## 4. Corollary B (explicit, verifiable). PROVED given I1–I3
On the 2D torus with even side L/eps, with chi_L the continuum susceptibility (= eps^2 chi):
  theta <= Theta := 12 lambda chi_L^2 / L^2 + min( 13.73 lambda chi_L , 0.2825 lambda L^2 ).
Hence (FD_kappa) holds for kappa >= 1/((1-Theta)(1 - 8 lambda chi_L^2/L^2)) whenever Theta < 1; e.g. (FD_2) on {Theta <= 0.34}.
Proof. Parseval: \int G^2 = L^-2 sum_k Ghat_c(k)^2 over continuum momenta k in BZ subset (2pi/L) Z^2, Ghat_c(k) = eps^2 Ghat(eps k).
By (I3) and sin^2(u/2) >= u^2/pi^2 on |u| <= pi: E(eps k) >= (4/pi^2) eps^2 |k|^2, so Ghat_c(k) <= C/|k|^2 with C = pi^2/4; also Ghat_c <= chi_L.
k = 0 gives chi_L^2. For k = 2 pi n/L, n != 0: with f(r) = min(A, B/r^2)^2, A = chi_L, B = C L^2/(4 pi^2):
 (a) sum_{n!=0} f(|n|) <= c^2 \int_{R^2} f = 2 pi c^2 A B, c = 1 + 1/sqrt2 (for y in n + [-1/2,1/2]^2, |y| <= c|n|, f decreasing);
 (b) sum_{n!=0} f(|n|) <= B^2 sum_{n!=0} |n|^-4 = 4 zeta(2) beta(2) B^2 = 6.0268 B^2.
Multiply by 12 lambda / L^2: (a) gives 12 c^2 C/(2pi) lambda chi_L = 13.73 lambda chi_L; (b) gives 12*6.0268 C^2/(16 pi^4) lambda L^2 = 0.2825 lambda L^2. ∎
(The constant 13.73 is about 14 times the Gaussian value 0.95: crude but explicit.)

## 5. Proposition C (conditional converse of Fable's Thm 4). PROVED (elementary)
Suppose on [a, a+delta], delta = 4 b kappa' m2(a): (P0_kappa) -d_u m2 >= |B(u)| / (12 b kappa) and G(u) := |B(u)|/m2(u) >= G(a).
Then (FD_kappa') holds at a provided kappa'/kappa >= -3 ln(1 - |B(a)|/3)/|B(a)| (<= 1.648).
Proof: psi(u) = m2(a+u): -psi' >= G(a) psi/(12 b kappa), so psi(delta) <= psi(0) exp(-|B(a)| kappa'/(3kappa)) <= (1 - |B(a)|/3) psi(0). ∎
Caveat (CN, rings in thmA_test.out; HEUR, G ~ g xi^eta): G is NOT monotone in a in the disordered phase (it decreases with a there), so this converse is usable only on the ordered side.
