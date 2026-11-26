"""Curie-Weiss phi^4 (numpy): weight exp(J/(2N)(sum phi)^2 + H sum phi - sum(a phi^2+b phi^4)).
HS: Z = int dy exp(-N y^2/(2J)) z(y+H)^N ; m = E_y[<x>_{y+H}].
Flip regime x = N H M: r = (-d_a m)/(2 m chi). A site-pivotal (vEHL-type with phi^2 insertion) lower bound
-d_a m >= kappa * (decoupled term 2 m chi) would need r >= kappa uniformly in N."""
import numpy as np
from scipy.special import logsumexp
X = np.linspace(-6, 6, 3001); dx = X[1]-X[0]
Y = np.linspace(-8, 8, 8001)
def m_of(a, b, J, H, N):
    T = (Y + H)[:, None]
    E = -a*X**2 - b*X**4 + T*X
    lz = logsumexp(E, axis=1) + np.log(dx)
    k1 = np.exp(logsumexp(E, axis=1, b=np.broadcast_to(np.maximum(X, 0), E.shape)) - lz - np.log(1)+np.log(dx)) \
       - np.exp(logsumexp(E, axis=1, b=np.broadcast_to(np.maximum(-X, 0), E.shape)) - lz + np.log(dx))
    f = -N*Y**2/(2*J) + N*lz
    w = np.exp(f - f.max())
    return (w*k1).sum()/w.sum()
a, b, J = 0.6, 1.0, 4.0
# bulk M: maximiser of -y^2/(2J)+logz(y)
T = Y[:, None]; E = -a*X**2 - b*X**4 + T*X; lz = logsumexp(E, axis=1)
ystar = Y[np.argmax(-Y**2/(2*J) + lz)]; M = abs(ystar)/J
print(f"a={a} b={b} J={J}: bulk M ~ {M:.4f}")
for N in [64, 256, 1024, 4096, 16384]:
    for x in [0.3, 1.0, 3.0]:
        H = x/(N*M); m = m_of(a, b, J, H, N)
        dh = H*1e-3; da = 1e-4
        chi = (m_of(a, b, J, H+dh, N) - m_of(a, b, J, H-dh, N))/(2*dh)
        dam = -(m_of(a+da, b, J, H, N) - m_of(a-da, b, J, H, N))/(2*da)
        r = dam/(2*m*chi)
        print(f"  N={N:6d} x={x:3.1f}: m={m:.5f} chi={chi:.4e} -d_a m={dam:.4e} 2m chi={2*m*chi:.4e} r={r:.3e} N*r={N*r:.3f}")
