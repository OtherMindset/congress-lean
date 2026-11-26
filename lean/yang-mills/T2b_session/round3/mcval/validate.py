"""Validation: (1) 2x2 torus (= 4-cycle with coupling 2, since each neighbouring pair is joined by
two torus bonds) by transfer-matrix quadrature; (2) Gaussian b=0 on 16x16 (chi = 1/(2a-4),
<phi^2> = G(0)); (3) the exact EOM (4-2a)m - 4b<C> + H = 0 on every run (done in run scripts)."""
import numpy as np, sys
from ana import load, direct, reweight_sym

def exact2x2(a, b, H):
    x = np.linspace(-7, 7, 2801); dx = x[1] - x[0]
    V = a * x**2 + b * x**4 - H * x
    T = np.exp(2 * np.outer(x, x) - 0.5 * (V[:, None] + V[None, :])) * dx
    T4 = np.linalg.matrix_power(T, 4); Z = np.trace(T4)
    mom = lambda k: np.trace(np.diag(x**k) @ T4) / Z
    return mom(1), mom(2), mom(3)

def exact_obs(a, b, H, dh=1e-4):
    m, B, C = exact2x2(a, b, H)
    mp, Bp, Cp = exact2x2(a, b, H + dh); mm, Bm, Cm = exact2x2(a, b, H - dh)
    chi = (mp - mm) / (2 * dh); dB = (Bp - Bm) / (2 * dh); dC = (Cp - Cm) / (2 * dh)
    R = (C - m * B) / m
    Rp = (Cp - mp * Bp) / mp; Rm = (Cm - mm * Bm) / mm
    return dict(m=m, B=B, C=C, chi=chi, R=R, dRdH=(Rp - Rm) / (2 * dh), D=dB)

def show(tag, est, ex):
    for k in ['m', 'B', 'C', 'chi', 'R', 'dRdH']:
        v, e = est[k]
        print(f"{tag} {k:5s} MC {v: .6f} +- {e:.6f}  exact {ex[k]: .6f}  pull {(v-ex[k])/e: .2f}")

if __name__ == '__main__':
    d = load('validation/v2x2_a.bin'); show('2x2 a=1.5 b=0.5 H=0.3', direct(d, 4), exact_obs(1.5, 0.5, 0.3))
    d = load('validation/v2x2_b.bin')
    for H in [0.05, 0.3]:
        show(f'2x2 a=1.8 b=0.1 H=0 rw->{H}', reweight_sym(d, 4, H), exact_obs(1.8, 0.1, H))
    # Gaussian
    L = 16; a = 2.5
    k = 2 * np.pi * np.arange(L) / L
    lam = 2 * a - 2 * np.cos(k)[:, None] - 2 * np.cos(k)[None, :]
    G0 = np.mean(1 / lam)
    d = load('validation/vgauss.bin'); e = direct(d, L * L)
    print(f"gauss16 <phi^2> MC {e['B'][0]:.5f} +- {e['B'][1]:.5f} exact {G0:.5f}")
    A = d[:, 0]; chi = L * L * np.mean(A**2)
    print(f"gauss16 chi MC {chi:.4f} exact {1/(2*a-4):.4f}")
