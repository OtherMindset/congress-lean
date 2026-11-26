import numpy as np,sys
N=int(sys.argv[1])
D=np.load(f'cw_N{N}.npy'); ys,lp,sg,t3=D.T; dy=ys[1]-ys[0]; n=len(ys)
p=np.exp(lp-lp.max()); p/=p.sum()
def direct(H):
    w=p*np.exp(N*H*ys-(N*H*ys).max()); w/=w.sum()
    m=(w*ys).sum(); return m,(w*t3).sum()/m-(w*sg).sum(),(w*sg).sum()
# pair quantities on w=y_i+y_j
Pw={};Aw={};Gw={}
I,Jx=np.meshgrid(np.arange(n),np.arange(n),indexing='ij')
k=(I+Jx).ravel(); pp=(p[:,None]*p[None,:]).ravel()
A=(t3[:,None]+t3[None,:]-sg[:,None]*ys[None,:]-sg[None,:]*ys[:,None]).ravel()
G=((sg[:,None]-sg[None,:])*(ys[:,None]-ys[None,:])).ravel()
P=np.bincount(k,pp,2*n-1); PA=np.bincount(k,pp*A,2*n-1); PG=np.bincount(k,pp*G,2*n-1)
wv=2*ys[0]+dy*np.arange(2*n-1)
pos=(wv>1e-9)&(P>1e-300)
w=wv[pos]; Pw=P[pos]; Psi=PA[pos]/Pw/(2*w); Gam=N*PG[pos]/Pw/(2*w)
np.save(f'psi_N{N}.npy',np.c_[w,Pw,Psi,Gam])
print('N',N)
for H in [1e-4,3e-4,1e-3,3e-3,1e-2,3e-2,0.1,0.3]:
    m,R,s2=direct(H)
    pi=w*np.sinh(np.minimum(N*H*w,700))*Pw; pi/=pi.sum()
    print(f'H={H:g} m={m:.5f} R={R:.6f} 2<Psi>={2*(pi*Psi).sum():.6f} <Gam>={(pi*Gam).sum():.5f}')
# derivative check dphi2/dH vs 2m<Gam>
for H in [1e-3,1e-2]:
    e=1e-6*max(H,1e-3)
    d=(direct(H+e)[2]-direct(H-e)[2])/(2*e); m=direct(H)[0]
    pi=w*np.sinh(N*H*w)*Pw; pi/=pi.sum()
    print('dphi2/dH',d,'2m<Gam>',2*m*(pi*Gam).sum())
# shape of Psi where P_0 has mass
sel=Pw>1e-12*Pw.max()
ww=w[sel];ps=Psi[sel];gg=Gam[sel]
idx=np.linspace(0,len(ww)-1,25).astype(int)
for i in idx: print(f'w={ww[i]:.3f} logP={np.log(Pw[sel][i]):.2f} Psi={ps[i]:.5f} Gam={gg[i]:.4f}')
d=np.diff(ps); print('Psi monotone dec on support?',(d<=1e-10).all(),'max increase',d.max(), 'min Gam',gg.min())
