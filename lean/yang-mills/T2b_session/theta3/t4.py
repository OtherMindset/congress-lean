import numpy as np,sys,glob
# exact H-derivatives from saved CW conditional data
for f in sorted(glob.glob('cw_*_*_*_*.npy')):
    ys,lp,sg,t3=np.load(f).T; N=int(f.split('_')[-1][:-4])
    p=np.exp(lp-lp.max())
    out=[]
    for H in np.logspace(-3.5,0,71):
        w=p*np.exp(N*H*ys-(N*H*ys).max()); w/=w.sum()
        E=lambda g:(w*g).sum()
        m=E(ys); C=lambda g:N*(E(g*ys)-E(g)*m)
        chi=C(ys); dt3=C(t3); dS=C(sg)
        dR=dt3/m-E(t3)*chi/m**2-dS
        out.append((H,m,dR,dS))
    o=np.array(out); s=o[:,1]<=0.5
    r=o[s,2]/o[s,3]
    print(f, 'max dR/dH (m<=.5)=%.3e'%o[s,2].max(),' max dR/dphi2: %.3e'%r.max(), ' max dR*m^2/dphi2: %.3e'%(r*o[s,1]**2).max(), ' max m^1.5 ratio %.3e'%(r*o[s,1]**1.5).max())
