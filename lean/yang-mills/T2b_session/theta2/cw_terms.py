# Curie-Weiss phi^4 via Hubbard-Stratonovich, exact in N (1-d quadrature).
# weight exp((J/2N)Phi^2 + h Phi - sum(a phi^2 + b phi^4)), Phi = sum phi_i.
# Computes the three cumulant terms of m^2 dR/dh (lattice units) and S = d<phi0^2>/dh
# to show the volume-order cancellation in the flip regime.
import numpy as np, sys
def site(a,b,ks):
    ph=np.linspace(-6,6,3001); dp=ph[1]-ph[0]
    E=-a*ph**2-b*ph**4
    A=E[None,:]+np.outer(ks,ph); mx=A.max(1,keepdims=True); w=np.exp(A-mx)
    z=w.sum(1)*dp; lz=np.log(z)+mx[:,0]
    mu=[ (w*ph**k).sum(1)*dp/z for k in range(1,5)]
    return lz,mu
def run(a,b,J,N,h):
    # y = k (site tilt) ; weight  exp(-N (k-h)^2/(2J) + N log z(k))
    ks=np.linspace(-8,8,8001)
    lz,mu=site(a,b,ks)
    lw=-N*(ks-h)**2/(2*J)+N*lz; lw-=lw.max(); w=np.exp(lw); w/=w.sum()
    E=lambda f:(w*f).sum()
    D=N*(ks-h)/J                         # d/dh log weight (up to const)
    dE=lambda f:E(f*D)-E(f)*E(D)          # d/dh E[f]
    m=E(mu[0]); M2=E(mu[1]); M3=E(mu[2])
    chi=dE(mu[0]); G=M2-m*m
    u3=M3-3*m*M2+2*m**3
    U3=dE(mu[1])-2*m*chi                 # dG/dh
    U4=dE(mu[2])-3*chi*M2-3*m*dE(mu[1])+6*m*m*chi   # du3/dh
    S=dE(mu[1])
    return m,chi,u3,U3,U4,S
if __name__=="__main__":
    a,b,J=float(sys.argv[1]),float(sys.argv[2]),float(sys.argv[3])
    for N in [64,256,1024,4096]:
        # magnetisation scale at h=0+: use M from large field-free estimate
        m0,_,_,_,_,_=run(a,b,J,N,0.05)
        for x in [0.3,1.0]:
            h=x/(N*m0)
            m,chi,u3,U3,U4,S=run(a,b,J,N,h)
            t1=m*U4; t2=2*m*m*U3; t3=-chi*u3
            print(f"N={N:5d} x={x:3.1f} m={m:.4f} chi={chi:9.2f} | mU4={t1:10.3f} 2m^2U3={t2:10.3f} -chi*u3={t3:10.3f} sum={t1+t2+t3:9.4f} | S={S:8.4f} 2m*chi={2*m*chi:9.2f}  m-h*chi={m-h*chi:.3e} 4bm^2(sum/m^2+S)={4*b*(t1+t2+t3+m*m*S):.3e}")
