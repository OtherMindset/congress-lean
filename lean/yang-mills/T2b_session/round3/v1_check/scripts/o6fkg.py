# (O6) <q0 q1^2 q2^2><q0> >= <q0 q1^2><q0 q2^2> on path 1-0-2, homogeneous masses.
# weight exp(J(q0q1+q0q2) + h(q0+q1+q2) - sum(A q^2 + c q^4)); exact: integrate leaves analytically by 1D quadrature
import numpy as np, itertools
x,w=np.polynomial.legendre.leggauss(800); L=6.0; x*=L; w*=L
def margin(A,c,J,h):
    site=w*np.exp(-A*x**2-c*x**4)
    # leaf integrals as function of q0: I_k(q0)=int q^k e^{Jq0 q + h q} site(q)
    K=np.exp(J*np.outer(x,x)+h*x[None,:])*site[None,:]  # rows q0
    I0=K.sum(1); I2=(K*x**2).sum(1)
    base=site*np.exp(h*x)  # q0 weight
    Z=(base*I0*I0).sum()
    e=lambda f:(base*f).sum()/Z
    q0=x
    m=e(q0*I0*I0); l=e(q0*I2*I2)*m; r=e(q0*I2*I0)**2
    return (l-r)/r
best=(1,None)
for A in np.linspace(1.8,2.2,9):
  for c in (0.162,0.081):
    for J in np.linspace(0.6,1.1,11):
        v=margin(A,c,J,0.031)
        if v<best[0]: best=(v,(A,c,J))
    print('A=%.2f c=%.3f'%(A,c),' '.join('%+.4f'%margin(A,c,J,0.031) for J in (0.7,0.8,0.9,1.0)))
print('best',best)
# convergence check
x,w=np.polynomial.legendre.leggauss(1600); L=7.0; x*=L; w*=L
print('conv',margin(2.0,0.081,0.85,0.031),margin(2.0,0.162,0.85,0.031))
