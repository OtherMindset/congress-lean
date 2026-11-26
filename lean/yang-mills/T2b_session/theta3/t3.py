import numpy as np,sys; sys.path.insert(0,'.')
from cw import *
a,b,J,N=float(sys.argv[1]),float(sys.argv[2]),float(sys.argv[3]),int(sys.argv[4])
ys=np.linspace(-2.2,2.2,441); dy=ys[1]-ys[0]
C=cond(N,ys,a,b); lp=C[:,0]+J*N*ys**2/2; sg=C[:,1]; t3=C[:,2]
np.save(f'cw_{a}_{b}_{J}_{N}.npy',np.c_[ys,lp,sg,t3])
p=np.exp(lp-lp.max()); p/=p.sum()
def direct(H):
    w=p*np.exp(N*H*ys-(N*H*ys).max()); w/=w.sum()
    m=(w*ys).sum(); return np.array([m,(w*t3).sum()/m-(w*sg).sum(),(w*sg).sum()])
n=len(ys); I,Jx=np.meshgrid(np.arange(n),np.arange(n),indexing='ij')
k=(I+Jx).ravel(); pp=(p[:,None]*p[None,:]).ravel()
A=(t3[:,None]+t3[None,:]-sg[:,None]*ys[None,:]-sg[None,:]*ys[:,None]).ravel()
G=((sg[:,None]-sg[None,:])*(ys[:,None]-ys[None,:])).ravel()
P=np.bincount(k,pp,2*n-1); PA=np.bincount(k,pp*A,2*n-1); PG=np.bincount(k,pp*G,2*n-1)
wv=2*ys[0]+dy*np.arange(2*n-1); pos=(wv>1e-9)&(P>1e-200)
w=wv[pos]; Pw=P[pos]; Psi=PA[pos]/Pw/(2*w); Gam=N*PG[pos]/Pw/(2*w)
sel=Pw>1e-10*Pw.max(); d=np.diff(Psi[sel])
print(f'a={a} b={b} J={J} N={N}: Psi max increase {d.max():.3e} (Psi range {Psi[sel].min():.3f}..{Psi[sel].max():.3f}), min Gam {Gam[sel].min():.3e}, sigma monotone in |y|: {(np.diff(sg[ys>=0])>=-1e-9).all()}')
# local maxima of P
lP=np.log(Pw); pk=[w[i] for i in range(1,len(w)-1) if lP[i]>lP[i-1] and lP[i]>lP[i+1]]
print('  P_0 peaks at w =',np.round(pk,3),' (w=0 is boundary)')
Hs=np.logspace(-5,0,60); vals=np.array([direct(H) for H in Hs])
worst={}
for i,H in enumerate(Hs):
    e=H*1e-4; dp_=(direct(H+e)-direct(H-e))/(2*e)
    m=vals[i,0]; dR=dp_[1]; dS=dp_[2]
    for th in [0,0.5,1]:
        Kn=dR*m**(2-th)/dS
        if m<=0.5: worst[th]=max(worst.get(th,-1e9),Kn)
    if i%6==0: print(f'  H={H:.2e} m={m:.4f} chi*H/m={dp_[0]*H/m:.3f} dR/dH={dR:.3e} dphi2/dH={dS:.3e}')
print('  max over m<=0.5 of dR*m^(2-th)/dphi2 for th=0,0.5,1:',{t:round(v,5) for t,v in worst.items()})
