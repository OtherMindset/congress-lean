# Two-site (transitive) exact check of the walk identities of NOTES.md:
#   weight exp(J phi0 phi1 + H(phi0+phi1) - sum(a phi^2 + b phi^4)).
#   BFS walk measure from 0: w0(dt) = H sum_n J^n rho_{k0}(t0) rho_{k1}(t1) Z(t)/Z dt.
# Checks: (1) m = int w0 ; (2) H T = int w0 m_0^{(t)} <= m^2 ;
#         (3) m - H chi = H int w0 sum_y (m - m_y^{(t)}) ;  (4) K_eff = (m-Hchi)/(4b H T S).
# Here m^{(t)} = <phi> under site weights g(phi^2/2 + t_z) (masses a + 4b t_z).
import numpy as np, sys
from scipy.special import gammaln
a,b,J,H=[float(x) for x in sys.argv[1:5]]
ph=np.linspace(-6,6,int(sys.argv[7]) if len(sys.argv)>7 else 241); P0,P1=np.meshgrid(ph,ph,indexing='ij'); S0,S1=P0**2/2,P1**2/2
base=J*P0*P1+H*(P0+P1)
def env(t0,t1):
    lw=base-2*a*(S0+t0)-4*b*(S0+t0)**2-2*a*(S1+t1)-4*b*(S1+t1)**2
    c=lw.max(); w=np.exp(lw-c); Z=w.sum()
    return np.log(Z)+c, (w*P0).sum()/Z, (w*P1).sum()/Z
F00,m,_=env(0,0)
w=np.exp(base-a*(P0**2+P1**2)-b*(P0**4+P1**4)); w/=w.sum()
E=lambda f:(w*f).sum()
chi=E(P0*(P0+P1))-m*2*m; S=E(P0*(P0**2+P1**2))-m*E(P0**2+P1**2)
tmax=float(sys.argv[5]) if len(sys.argv)>5 else 12.0; nt=int(sys.argv[6]) if len(sys.argv)>6 else 97
ts=np.linspace(0,tmax,nt); dt=ts[1]-ts[0]
T0,T1=np.meshgrid(ts,ts,indexing='ij')
lt0=np.log(np.maximum(T0,1e-300)); lt1=np.log(np.maximum(T1,1e-300))
# kernel sum over n>=1 (log-sum-exp)
terms=[]
for j in range(1,120):
    terms.append((2*j-1)*np.log(J)+(j-1)*(lt0+lt1)-2*gammaln(j))
    terms.append(2*j*np.log(J)+j*lt0+(j-1)*lt1-gammaln(j+1)-gammaln(j))
terms=np.array(terms); mx=terms.max(0); Kn=np.exp(mx)*np.exp(terms-mx).sum(0)
Fg=np.zeros_like(T0); M0=np.zeros_like(T0); M1=np.zeros_like(T0)
for i in range(nt):
    for k in range(nt):
        Fg[i,k],M0[i,k],M1[i,k]=env(ts[i],ts[k])
Wt=H*Kn*np.exp(Fg-F00)            # density on (t0,t1)
Wa=H*np.exp(Fg[:,0]-F00)          # atom n=0: t1=0, density 1 in t0
tw=np.full(nt,dt); tw[0]=tw[-1]=dt/2
I2=lambda f: (tw[:,None]*tw[None,:]*Wt*f).sum()+(tw*Wa*f[:,0]).sum()
mrw=I2(np.ones_like(T0)); HT=H*I2(T0+T1)/H*H  # H*T where T=int w0 |t|
HT=H*I2(T0+T1)
HTalt=I2(M0)
loss=H*I2((m-M0)+(m-M1))
print(f"a={a} b={b} J={J} H={H}: m={m:.6f} m_RW={mrw:.6f}  tail w0(t>tmax/2)={I2((T0>tmax/2)|(T1>tmax/2))/mrw:.1e}")
print(f"  HT={HT:.6e}  int w0 m0^(t)={HTalt:.6e}  HT/m^2={HT/m**2:.4f}")
print(f"  m-Hchi={m-H*chi:.6e}  H int w0 sum_y(m-m_y^(t))={loss:.6e}")
print(f"  K_eff=(m-Hchi)/(4b HT S)={(m-H*chi)/(4*b*HT*S):.4f}   Lemma-L ratio (m-Hchi)/(8b m^2 S)={(m-H*chi)/(8*b*m*m*S):.4f}")
