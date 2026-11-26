# 1D ring phi^4: weight exp(J sum phi_x phi_{x+1} - sum(a phi^2+b phi^4) + H sum phi). Transfer operator.
import numpy as np,sys
def build(a,b,J,H,ph,dp):
    V=a*ph**2+b*ph**4-H*ph
    T=np.exp(J*np.outer(ph,ph)-0.5*(V[:,None]+V[None,:]))*dp
    return T
def spec(a,b,J,H,ph,dp):
    lam,U=np.linalg.eigh(build(a,b,J,H,ph,dp)); return lam[::-1],U[:,::-1]
def moments(a,b,J,H,N,ph,dp):
    lam,U=spec(a,b,J,H,ph,dp)
    w=(lam/lam[0])**N; w=np.where(np.abs(lam/lam[0])<1e-300,0,w)
    Z=w.sum()
    out=[]
    for k in (1,2,3):
        d=np.einsum('ik,i,ik->k',U,ph**k,U); out.append((w*d).sum()/Z)
    return np.array(out)
if __name__=='__main__':
    a,b,J=map(float,sys.argv[1:4]); pm=float(sys.argv[4]) if len(sys.argv)>4 else 6
    ph=np.linspace(-pm,pm,401); dp=ph[1]-ph[0]
    lam,_=spec(a,b,J,0,ph,dp); xi=1/np.log(lam[0]/lam[1]); print(f'a={a} b={b} J={J}: xi={xi:.2f}')
    for N in [int(max(4,f*xi)) for f in (0.3,1,3,10)]:
        Hs=np.logspace(-6,0.5,140); M=np.array([moments(a,b,J,H,N,ph,dp) for H in Hs])
        m=M[:,0]; R=(M[:,2]-m*M[:,1])/m
        dR=np.diff(R); mm=0.5*(m[1:]+m[:-1])
        # chi via derivative of m in log H
        chiH=np.gradient(m,np.log(Hs))   # = H chi
        print(f'  N={N}: chi(H->0)~{m[0]/Hs[0]:.3g}; max rel increase of R between grid pts: {(dR/R[1:]).max():.2e}; R range {R.min():.3f}..{R.max():.3f}; Hchi/m at m~0.3*max: {np.interp(0.3*m.max(),m,chiH/m):.3f}')
