import numpy as np, sys
def psi_curve(a,b,J,vs,L=4.5,n=90):
    g=np.linspace(-L,L,n); A,B,C=np.meshgrid(g,g,g,indexing='ij')  # phi0, phi1, phi0'
    V=lambda x:a*x**2+b*x**4
    out=[]
    for v in vs:
        D=v-A-B-C  # phi1'
        lw=-V(A)-V(B)-V(C)-V(D)+J*(A*B+C*D)
        w=np.exp(lw-lw.max())
        F=(A+C)*(A-C)**2+(B+D)*(B-D)**2
        out.append((w*F).sum()/w.sum()/v)
    return np.array(out)
vs=np.linspace(0.1,5,25)
worst=-np.inf
for a in [-1.5,-0.5,0.5,1.5]:
    for J in [0.2,0.7,1.5]:
        p=psi_curve(a,1,J,vs); d=np.diff(p).max()/np.abs(p).max()
        print(a,J,'max rel incr',round(d,5),np.round(p[::6],4),flush=True)
