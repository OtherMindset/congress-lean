# Brute-force check on an N=3 ring (J per bond; c = 2a-2J) of the zero-mode Cauchy-Schwarz inequality (Z):
#   Var(Y^2) * Var(G0) >= Cov(Y^2,G0)^2 = 4 m2^2,  G0 = Y*sum_x d_x S = Y*(c M + 4 b Phi3),
#   Var(G0) = 1 + E[Y^2 sum_x (c + 12 b phi_x^2)] = (1 + chi*mH2)/2 + 6 b * Cov(Y^2,Phi2),   chi = N m2, mH2 = c+12b<phi0^2>
# and (E'):  Var(Phi2)*Var(G0) >= Cov(Phi2,G0)^2 = 4 N^2 m2^2.
import numpy as np
def run(a,b,J,n=121,R=None):
    N=3
    if R is None:
        R=1.0
        while (a-J)*R*R+b*R**4<30: R+=0.05
    x=np.linspace(-R,R,n); X1,X2,X3=np.meshgrid(x,x,x,indexing='ij')
    S=a*(X1**2+X2**2+X3**2)+b*(X1**4+X2**4+X3**4)-J*(X1*X2+X2*X3+X3*X1)
    w=np.exp(-(S-S.min())); w/=w.sum()
    E=lambda f:(w*f).sum()
    M=X1+X2+X3; Y=M/N; P2=X1**2+X2**2+X3**2; P3=X1**3+X2**3+X3**3
    c=2*a-2*J
    G0=Y*(c*M+4*b*P3)
    m2=E(Y**2); m4=E(Y**4)
    cov=lambda f,g:E(f*g)-E(f)*E(g)
    VG=cov(G0,G0); chi=N*m2; mH2=c+12*b*E(P2)/N
    print("a,b,J=",a,b,J)
    print("  E G0 =%.6f (1)   Cov(Y^2,G0)=%.6f (2m2=%.6f)   Cov(Phi2,G0)=%.6f (2N m2=%.6f)"%(E(G0),cov(Y**2,G0),2*m2,cov(P2,G0),2*N*m2))
    print("  Var G0=%.6f   1+E[Y^2 H]=%.6f   (1+chi mH2)/2+6b Cov(Y^2,Phi2)=%.6f"%(VG,1+E(Y**2*(N*c+12*b*P2)),(1+chi*mH2)/2+6*b*cov(Y**2,P2)))
    print("  (Z): Var(Y^2)*VarG0=%.6f >= 4m2^2=%.6f ;  (E'): Var(Phi2)VarG0=%.5f >= 4N^2m2^2=%.5f"%(cov(Y**2,Y**2)*VG,4*m2**2,cov(P2,P2)*VG,4*N*N*m2**2))
    B=m4/m2**2-3; D=cov(Y**2,P2)
    print("  |B|=%.4f ; bound (2-|B|)*[ (chi mH2-1)/2 + 6b(-d_a m2) ] = %.4f ; pieces: hartree defect=%.4f, 6b(-d_a m2)=%.4f"%(abs(B),(2-abs(B))*((chi*mH2-1)/2+6*b*D),(chi*mH2-1)/2,6*b*D))
for p in [(1.2,0.1,1.0),(0.9,0.1,1.0),(0.5,0.5,1.0),(-1.0,0.5,1.0),(0.7,0.02,1.0)]: run(*p)
