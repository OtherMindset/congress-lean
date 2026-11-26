import numpy as np
t=np.linspace(-7,7,1401)
def marg(V,qg):
    W=V((qg[:,None]+t)/np.sqrt(2))+V((qg[:,None]-t)/np.sqrt(2)); lw=-W; mx=lw.max(1,keepdims=True); w=np.exp(lw-mx)
    lr=np.log(w.sum(1))+mx[:,0]; g=(w*t**2).sum(1)/w.sum(1); return lr,g
qg=np.linspace(-7,7,2801); dq=qg[1]-qg[0]
for a in [-4,-2,-1,0,1,3]:
    V=lambda x:a*x**2+x**4
    lr,g=marg(V,qg)
    for N in [2,3]:
        us=np.linspace(0.05,5,100); psi=[]
        # density of sum of other N-1 q's
        if N==2: lo=lambda s: np.interp(s,qg,lr,left=-1e9,right=-1e9)
        else:
            r=np.exp(lr-lr.max()); c=np.convolve(r,r)*dq; sg=np.linspace(2*qg[0],2*qg[-1],len(c)); lc=np.log(np.maximum(c,1e-300))
            lo=lambda s: np.interp(s,sg,lc,left=-1e9,right=-1e9)
        for u in us:
            l=lr+lo(u-qg); w=np.exp(l-l.max())
            psi.append(N*(w*qg*g).sum()/w.sum()/u)
        psi=np.array(psi); d=np.diff(psi)
        print('a',a,'N',N,'max rel increase',d.max()/psi.max(),'psi',np.round(psi[::20],4))
