import numpy as np, glob, re, os
runs='/home/claude/t2b/mc/runs/'
def cum(w,A,B):
    w=w/w.sum(); mA=w@A; mB=w@B
    dA=A-mA; dB=B-mB
    return w@(dA*dB*dB)
def jk(A,B,w,N,nb=50):
    n=len(A); idx=np.arange(n)*nb//n
    full=cum(w,A,B)*N*N
    rep=np.array([cum(w[idx!=j],A[idx!=j],B[idx!=j])*N*N for j in range(nb)])
    return full, np.sqrt((nb-1)*np.mean((rep-rep.mean())**2))
out=[]
files=[f for f in sorted(glob.glob(runs+'b*.bin'))]
byk={}
for f in files:
    m=re.match(r'b([\d.e-]+)_a([\d.]+)_L(\d+)_H([\d.e-]+?)\.bin',os.path.basename(f))
    b,a,L,H=float(m[1]),float(m[2]),int(m[3]),float(m[4])
    d=np.fromfile(f).reshape(-1,4)[:,:3]
    N=L*L; A,B=d[:,0],d[:,1]
    byk.setdefault((b,a,L),{})[H]=d
    if H>0:
        v,e=jk(A,B,np.ones(len(A)),N); out.append(('direct',b,a,L,H,H*np.abs(N*A).mean(),v,e))
for (b,a,L),dd in byk.items():
    if 0.0 not in dd: continue
    d=dd[0.0]; N=L*L; A,B=d[:,0],d[:,1]; M0=np.abs(N*A).mean()
    AA=np.concatenate([A,-A]); BB=np.concatenate([B,B]); MM=N*AA
    n=len(A); idx=np.arange(n)*50//n; idx2=np.concatenate([idx,idx])
    for s in [0.1,0.3,1,3]:
        H=s/M0
        def f(mask):
            x=H*MM[mask]; w=np.exp(x-x.max()); return cum(w,AA[mask],BB[mask])*N*N
        full=f(np.ones(2*n,bool)); rep=np.array([f(idx2!=j) for j in range(50)])
        e=np.sqrt(49*np.mean((rep-rep.mean())**2))
        out.append(('rew',b,a,L,H,s,full,e))
import pickle; pickle.dump(out,open('mc3.pkl','wb'))
O=np.array([(o[1],o[2],o[3],o[4],o[5],o[6],o[7]) for o in out]); kind=np.array([o[0] for o in out])
z=O[:,5]/O[:,6]
print('total',len(O))
for k in ['direct','rew']:
    s=kind==k; print(k,'n',s.sum(),'neg',(O[s,5]<0).sum(),'z<-2',(z[s]<-2).sum(),'z<-3',(z[s]<-3).sum(),'z>3',(z[s]>3).sum(),'min z',z[s].min(),'max z',z[s].max())
    i=np.argmin(np.where(s,z,1e9)); print(' worst',O[i],z[i])
    i=np.argmax(np.where(s,z,-1e9)); print(' best',O[i],z[i])
