"""Empirical 2-kernel growth check for monotone von Neumann outer-totalistic rules (e.g. Rule 750).

Usage:  python3 r750_kernel_check.py RULE WINDOW MAXDEPTH LOG2N
        python3 r750_kernel_check.py 750 32 6 12     # Rule 750, window 32, depths 0..6, data x,y < 4096
        python3 r750_kernel_check.py 686 16 6 12     # control: Ulam-Warburton

Diagram as in the paper's eq. (1): D(x,y,t) = s_{R,t-1}(x,y) for x,y >= 0, t >= 1.
For a monotone rule (ON never turns OFF) D(x,y,t) = 1 iff T(x,y) <= t-1, where T is the birth stage.
Kernel element (j; a,b,c): (x,y,t) -> D(2^j x + a, 2^j y + b, 2^j t + c).
On the window x,y,t < w it is determined by F(x,y) = clip(ceil((T(2^j x+a, 2^j y+b) + 1 - c) / 2^j), 0, w),
the first t at which the cell is ON in that element. Counting distinct F per depth is the window
identification the guesser uses. For an automatic diagram the per-depth count stays bounded (by the
number of states) and stops producing new elements; it cannot prove or refute automaticity, since
any finite window can merge distinct elements.
"""
import sys
import numpy as np


def birth_times(R, N):
    bits = np.array([(R >> i) & 1 for i in range(10)], dtype=np.uint8)
    q = np.zeros((N + 1, N + 1), dtype=np.uint8)
    q[0, 0] = 1
    T = np.full((N + 1, N + 1), 10**6, dtype=np.int64)
    T[0, 0] = 0
    for g in range(N - 1):
        k = np.zeros_like(q)
        k[:-1, :] += q[1:, :]
        k[1:, :] += q[:-1, :]
        k[0, :] += q[1, :]          # mirror: neighbour at x = -1 equals x = 1
        k[:, :-1] += q[:, 1:]
        k[:, 1:] += q[:, :-1]
        k[:, 0] += q[:, 1]
        new = bits[q + 2 * k]
        if ((q == 1) & (new == 0)).any():
            sys.exit(f"Rule {R} is not monotone; this check applies only to monotone rules.")
        T[(new == 1) & (q == 0)] = g + 1
        q = new
    return T


def counts_at_powers(T, nmax):
    out = []
    for n in range(nmax + 1):
        g = 2**n - 1
        w = (T[: g + 1, : g + 1] <= g)
        out.append(int(4 * w[1:, 1:].sum() + 2 * w[0, 1:].sum() + 2 * w[1:, 0].sum() + w[0, 0]))
    return out


def main():
    R, w, J, L = (int(a) for a in sys.argv[1:5])
    N = 2**L
    assert 2**J * w <= N, "data too small for this depth and window"
    T = birth_times(R, N)
    print(f"Rule {R}: counts at stages 2^n-1, n=0..{L}:", counts_at_powers(T, L))
    allseen = set()
    for j in range(J + 1):
        P = 2**j
        seen = set()
        for a in range(P):
            for b in range(P):
                Tp = T[a : a + P * w : P, b : b + P * w : P][:w, :w]
                for c in range(P):
                    seen.add(np.clip(-((c - 1 - Tp) // P), 0, w).astype(np.uint8).tobytes())
        new = len(seen - allseen)
        allseen |= seen
        print(f"Rule {R} w={w} depth {j}: distinct {len(seen)}, new {new}, cumulative {len(allseen)}", flush=True)


if __name__ == "__main__":
    main()
