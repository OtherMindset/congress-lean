# (A): is pi_h(|t|) ∝ cosh(J u0 u1) * ∫dq e^{-W(q0,u0)-W(q1,u1)+J q0 q1 + h(q0+q1)} q0  log-supermodular in (u0,u1)?
import numpy as np
q=np.linspace(-5,5,201); Q0,Q1=np.meshgrid(q,q,indexing='ij')
u=np.linspace(0.02,3.5,45)
def W(qq,tt,a,b):
    x=(qq+tt)/np.sqrt(2); y=(qq-tt)/np.sqrt(2); return a*(x**2+y**2)+b*(x**4+y**4)
def test(a,b,J,h):
    L=np.zeros((len(u),len(u)))
    W0=[W(Q0,ui,a,b) for ui in u]; W1=[W(Q1,ui,a,b) for ui in u]
    base=J*Q0*Q1+h*(Q0+Q1)
    for i in range(len(u)):
        for j in range(len(u)):
            lw=base-W0[i]-W1[j]; mx=lw.max(); w=np.exp(lw-mx)
            L[i,j]=np.log((w*Q0).sum())+mx+np.log(np.cosh(J*u[i]*u[j]))
    m=L[:-1,:-1]+L[1:,1:]-L[:-1,1:]-L[1:,:-1]
    return m.min()
for a,b,J,h in [(2,0.1,1,0.1),(2,0.1,1,1.0),(2,1,1,0.3),(0.5,1,1,0.3),(0.5,1,0.3,0.05),(2,1,3,0.3),(-1,1,1,0.3)]:
    print(a,b,J,h,'min supermodularity cross',test(a,b,J,h),flush=True)
