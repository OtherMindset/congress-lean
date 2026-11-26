# One-site check of the screened random-walk decomposition (member B, round 2).
# Site weight e^{-a phi^2 - b phi^4 + h phi}; s = phi^2/2; g(s)=exp(-2as-4bs^2).
# w0(dt) = h Z(t)/Z dt on (0,inf) (one-site BFS walk measure), T = int t w0.
# Claims checked:
#  (E)  m - h chi = h int int w0 w0 (1 - e^{-B12}),  B12 = F(t1)+F(t2)-F(t1+t2)-F(0), F=log Z
#  (S)  S = <phi;phi^2> = 2 int w0 [ t - 8b int_0^1 C(ut) t du ],  C(t)=Var_t(s)
#  (D)  m - h chi <= 4 b (hT) S + E3,
#       E3 = 64 b^2 h int int w0 w0 t1 t2 int int du dv [C(u t1) - C(u t1 + v t2)]
import numpy as np, sys
def run(a,b,h,nt=161,tmax=None):
    ph=np.linspace(-8,8,3201); s=ph**2/2
    def stats(t):
        lw=h*ph-2*a*(s+t)-4*b*(s+t)**2; c=lw.max(); w=np.exp(lw-c)
        Z=np.trapezoid(w,ph); Es=np.trapezoid(w*s,ph)/Z; Vs=np.trapezoid(w*s*s,ph)/Z-Es**2
        return np.log(Z)+c, Vs
    F0,_=stats(0.0)
    if tmax is None:
        # local time scale: decay of Z(t)/Z
        tmax=1.0
        while stats(tmax)[0]-F0>-40: tmax*=1.5
    ts=np.linspace(0,tmax,nt)
    F=np.array([stats(t)[0] for t in ts]); C=np.array([stats(t)[1] for t in ts])
    w0=h*np.exp(F-F0)
    p=np.exp(h*ph-a*ph**2-b*ph**4); p/=np.trapezoid(p,ph)
    E=lambda f: np.trapezoid(f*p,ph)
    m=E(ph); m2=E(ph**2); m3=E(ph**3); chi=m2-m*m; S=m3-m*m2
    mrw=np.trapezoid(w0,ts); T=np.trapezoid(w0*ts,ts)
    Ff=lambda t: np.interp(t,ts,F,right=np.nan) if np.all(t<=tmax) else np.array([stats(x)[0] for x in np.atleast_1d(t)])
    Cf=lambda t: np.array([stats(x)[1] for x in np.atleast_1d(t)])
    # (S)
    us=np.linspace(0,1,41)
    intC=np.array([np.trapezoid(np.interp(us*t,ts,C),us) for t in ts])
    S_rw=2*np.trapezoid(w0*(ts-8*b*intC*ts),ts)
    # (E) and (D) on a coarser grid
    idx=np.arange(0,nt,2); t1=ts[idx]; W=w0[idx]
    T1,T2=np.meshgrid(t1,t1,indexing='ij')
    Fs=np.array([[stats(x+y)[0] for y in t1] for x in t1])
    Fi=F[idx]
    B=Fi[:,None]+Fi[None,:]-Fs-F0
    lhsE=h*np.trapezoid(np.trapezoid(W[:,None]*W[None,:]*(1-np.exp(-B)),t1,axis=1),t1)
    BB=h*np.trapezoid(np.trapezoid(W[:,None]*W[None,:]*B,t1,axis=1),t1)
    # E3
    uu=np.linspace(0,1,9); vv=np.linspace(0,1,9)
    E3int=np.zeros_like(T1)
    for i,x in enumerate(t1):
        Cu=np.interp(uu*x,ts,C)
        for j,y in enumerate(t1):
            Cuv=np.array([[stats(u*x+v*y)[1] for v in vv] for u in uu])
            E3int[i,j]=np.trapezoid(np.trapezoid(Cu[:,None]-Cuv,vv,axis=1),uu)
    E3=64*b*b*h*np.trapezoid(np.trapezoid(W[:,None]*W[None,:]*T1*T2*E3int,t1,axis=1),t1)
    lhs=m-h*chi
    print(f"a={a} b={b} h={h}: m={m:.6f} mRW={mrw:.6f} | m-hchi={lhs:.5e} (E)={lhsE:.5e} | S={S:.5e} S_rw={S_rw:.5e}")
    print(f"   h<<B>>={BB:.4e}  4b hT S={4*b*h*T*S:.4e}  E3={E3:.4e}  sum={4*b*h*T*S+E3:.4e}  [should equal h<<B>> ]")
    print(f"   ratios: (m-hchi)/(4bhTS)={lhs/(4*b*h*T*S):.3f}  E3/(4bhTS)={E3/(4*b*h*T*S):.3f}  hT/m^2={h*T/m**2:.3f}  8bm^2S/(m-hchi)={8*b*m*m*S/lhs:.3f}")
for a,b,h in [(2.0,0.05,0.3),(1.0,1.0,0.3),(-1.0,1.0,0.3),(-2.0,1.0,0.1)]:
    run(a,b,h)
