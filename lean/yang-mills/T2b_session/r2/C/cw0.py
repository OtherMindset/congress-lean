# Curie-Weiss phi^4 at h=0: torus quantities M_N^2, Binder B_N, -d_a M_N^2, and leading-Taylor (P0) constant.
# Also full sup r_theta from theta1's obs() for comparison.
import numpy as np, sys
sys.path.insert(0,'/home/claude/t2b/theta1')
from cw_theta import site, obs
def h0(S,J,N,W):
    g,p1,p2,p3=S
    w=np.linspace(-W,W,400001)
    lw=-N*w**2/(2*J)+N*g(w); lw-=lw.max(); P=np.exp(lw); P/=P.sum()
    k2=(P*w**2).sum(); k4w=(P*w**4).sum()-3*k2**2
    K2=(N/J)**2*k2-N/J; K4=(N/J)**4*k4w
    q2=p2(w); cov=(P*w**2*(q2-(P*q2).sum())).sum()
    M2=K2/N**2; B=K4/K2**2; dM2=N*cov/J**2   # -d_a M^2
    return M2,B,dM2,K2/N
if __name__=="__main__":
    a,b,J=[float(x) for x in sys.argv[1:4]]
    W=J*6+4; S=site(a,b,W+2)
    for N in [16,64,256,1024,4096]:
        M2,B,dM2,chi0=h0(S,J,N,W)
        hs=np.exp(np.linspace(np.log(1e-7),np.log(1.0),90))
        res=np.array([obs(S,J,N,h,W) for h in hs]); m,chi,dam=res[:,0],res[:,1],res[:,2]
        lhs=m-hs*chi
        line=f"N={N:5d} M_N={np.sqrt(M2):.4f} B={B:+.4f} -daM2={dM2:.4f} |B|/(-daM2)={abs(B)/dM2:.4f} G*s^2(s=.1)={abs(B)*.01/M2:.3g} |"
        for th in [1.0,1.5]:
            for s0 in [0.05,0.1,0.2]:
                sel=(m<=s0)&(m>1e-3*s0); full=(lhs/(4*b*m**th*dam))[sel].max()
                pred=s0**(2-th)*abs(B)/(12*b*dM2)
                line+=f" th{th} s{s0}: {full:.4f}/{pred:.4f}"
        print(line,flush=True)
