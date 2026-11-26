# 2-site, conditioned on Q=q0+q1=u: q0=u/2+v, q1=u/2-v. T1=E[(t0^2+t1^2)/2], T2=E[v(t0^2-t1^2)]/u
import numpy as np
g=np.linspace(-4.5,4.5,111); Vv,T0,T1=np.meshgrid(g,g,g,indexing='ij')
def W(q,t,a,b): return a*(q**2+t**2)+0.5*b*(q**4+6*q**2*t**2+t**4)
def parts(a,b,J,us):
    out=[]
    for u in us:
        lw=-W(u/2+Vv,T0,a,b)-W(u/2-Vv,T1,a,b)-J*Vv**2*2*0.5*2/2+J*T0*T1  # J q0 q1 = J(u^2/4 - v^2) -> -J v^2
        lw=-W(u/2+Vv,T0,a,b)-W(u/2-Vv,T1,a,b)-J*Vv**2+J*T0*T1
        w=np.exp(lw-lw.max()); w/=w.sum()
        t1=(w*(T0**2+T1**2)/2).sum(); t2=(w*Vv*(T0**2-T1**2)).sum()/u
        out.append((t1,t2,t1+t2))
    return np.array(out)
us=np.linspace(0.2,5,17)
for a,b,J in [(2,0.2,1),(2,1,1),(1,1,0.5),(0.5,1,1.5),(2,0.05,1.9),(3,1,0.3)]:
    P=parts(a,b,J,us); d=np.diff(P,axis=0)
    print(a,b,J,'T1 decr?',bool((d[:,0]<=1e-12).all()),'T2 sign range',np.round([P[:,1].min(),P[:,1].max()],4),'T2 decr?',bool((d[:,1]<=1e-12).all()),'Psi decr?',bool((d[:,2]<=1e-12).all()))
