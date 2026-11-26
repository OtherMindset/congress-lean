# (V2) ring: |B| = 12 b [ (-d_a m2) + R2/N ],  R = <phi0;phi0^2>/m, R2 = d^2R/dH^2 at 0. Independent computation of <phi0^k>.
import numpy as np
from ring import setup
def obs(a,b,J,N,H,ng=200):
    x,w=setup(a,b,J,ng)
    V=a*x*x+b*x**4-H*x
    T=np.exp(J*np.outer(x,x)-0.5*V[:,None]-0.5*V[None,:])*np.sqrt(w[:,None]*w[None,:])
    ev,U=np.linalg.eigh(T)
    lm=ev.max(); wt=(np.abs(ev)/lm)**N*np.sign(ev)**N
    Zt=wt.sum()
    return [ (wt*((U**2)*(x**k)[:,None]).sum(0)).sum()/Zt for k in (1,2,3)]
from ring import mom
for (a,b,J,N) in [(0.9,0.1,1.0,6),(0.5,0.5,1.0,4),(0.7,0.02,1.0,8)]:
    m2,m4=mom(a,b,J,N); B=m4/m2**2-3
    d=1e-4; D=-(mom(a+d,b,J,N)[0]-mom(a-d,b,J,N)[0])/(2*d)
    chi=N*m2; h=0.05/np.sqrt(N*chi)
    Rs=[]
    for k in (1,2,3):
        m,p2,p3=obs(a,b,J,N,k*h); Rs.append((p3-m*p2)/m)
    # R(H)=R0+R2 H^2/2+R4 H^4/24 ; three points
    A=np.array([[1,(k*h)**2/2,(k*h)**4/24] for k in (1,2,3)]); R0,R2,R4=np.linalg.solve(A,Rs)
    print(a,b,J,N,"|B|=%.6f   12b(-d_a m2 + R2/N)=%.6f   R2/(N*D)=%.4f"%(abs(B),12*b*(D+R2/N),R2/(N*D)))
