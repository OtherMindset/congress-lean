# Section 7.2 identities on 2 sites (single bond J): R/2 = E_pi[t0^2], d_eta R/2 = Cov_pi(t0^2, Phi)
import numpy as np
def R_direct(a,b,J,H,ng=400,L=4.):
    x,w=np.polynomial.legendre.leggauss(ng); x*=L; w*=L
    X0,X1=np.meshgrid(x,x,indexing='ij'); W=np.outer(w,w)
    P=W*np.exp(J*X0*X1+H*(X0+X1)-a*(X0**2+X1**2)-b*(X0**4+X1**4)); P/=P.sum()
    m=(P*X0).sum(); return ((P*X0**3).sum()-m*(P*X0**2).sum())/m
def cond(a,b,J,eta,ng=70,L=4.5):
    x,w=np.polynomial.legendre.leggauss(ng); x*=L; w*=L
    # W(q,t)= a q^2 + a t^2 + b/2 q^4 + 3b q^2 t^2 + b/2 t^4
    q0,q1=np.meshgrid(x,x,indexing='ij'); Wq=np.outer(w,w)
    t0,t1=q0,q1; Wt=Wq
    Nv=np.zeros((ng,ng)); Nq=np.zeros((ng,ng))
    for i in range(ng):
        for j in range(ng):
            T0,T1=x[i],x[j]
            E=J*q0*q1+eta*(q0+q1)-(a+3*b*T0**2)*q0**2-(a+3*b*T1**2)*q1**2-b/2*(q0**4+q1**4)
            base=Wq*np.exp(E)*np.exp(-(a*T0**2+b/2*T0**4+a*T1**2+b/2*T1**4))
            Nv[i,j]=(base*q0).sum(); Nq[i,j]=(base*q0*(q0+q1)).sum()
    pi=Wt*np.exp(J*t0*t1)*Nv; pi/=pi.sum()
    Phi=Nq/Nv
    Et=(pi*t0**2).sum()
    cov=(pi*t0**2*Phi).sum()-Et*(pi*Phi).sum()
    return Et,cov
for p in [(1.,0.5,0.5),(-1.,0.5,0.8)]:
    for H in (0.1,0.4):
        eta=np.sqrt(2)*H; d=1e-4
        Et,cov=cond(*p,eta)
        R=R_direct(*p,H); dR=(R_direct(*p,H+d)-R_direct(*p,H-d))/(2*d)
        print(p,H,'R/2=%.6f E_pi[t0^2]=%.6f | d_eta(R/2)=%.6f Cov=%.6f'%(R/2,Et,dR/2/np.sqrt(2),cov))
