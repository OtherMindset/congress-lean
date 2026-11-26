from t3 import *
import sys
def Sspin(n,edges,J,c,H):
    S,w=spin_data(n,edges,J,c,H); C=S@c
    def mom(idx):
        return np.prod(S[:,idx],axis=1)*1.0
    fs=[(np.array([0]),),]
    ev_=lambda F:ev(w,F)
    d=lambda F:ev_(F*C)-ev_(F)*ev_(C)
    s0,s1,s2=S[:,0]*1.,S[:,1]*1.,S[:,2]*1.
    terms=[(s0,s1*s2),(s1,s0*s2),(s2,s0*s1)]; t3=s0*s1*s2
    num=sum(ev_(a)*ev_(b) for a,b in terms); den=ev_(t3)
    dnum=sum(d(a)*ev_(b)+ev_(a)*d(b) for a,b in terms); dden=d(t3)
    Sv=num/den; dS=(dnum*den-num*dden)/den**2
    return Sv,H*dS/2   # P4 = (S-1)/2, returns H dP4/dH
def decomp(n,edges,J,wv,bc):
    A=np.array([1,1,1]+[0]*(n-3))
    Z=0;EK_=0;EF=0;EKF=0;t1=0;recs=[]
    for wt,d1,d2,cl in bc:
        a=(d1+A)%2;b=d2
        z=wt*Wgh(a,b,wv).prod()
        EKw=Kgh(a,b,wv).sum()
        comps=set(cl[:3]);pF=1.0;cov=0.0;pf=[]
        info=[]
        for r in comps:
            C=(cl==r); odd=((a+b)[C]>0).any()
            if odd: info.append((1.0,0.0))
            else:
                pa=1-np.prod(np.cosh(wv[C])**-2)   # P(attach)
                EKC=(2*wv[C]*np.tanh(wv[C])).sum()
                info.append((pa,EKC*(1-pa)))   # Cov(K_C,1[K_C>0]) = E[K_C]P(K_C=0)
        pF=np.prod([p for p,_ in info])
        for ii,(p,cv) in enumerate(info):
            cov+=cv*np.prod([q for jj,(q,_) in enumerate(info) if jj!=ii])
        recs.append((z,EKw,pF,cov))
    r=np.array(recs); Z=r[:,0].sum(); pz=r[:,0]/Z
    EK=(pz*r[:,1]).sum(); EFv=(pz*r[:,2]).sum()
    t1=(pz*r[:,3]).sum(); t2=(pz*r[:,1]*r[:,2]).sum()-EK*EFv
    return t1,t2
if __name__=="__main__":
    n=int(sys.argv[2]);worst=0;minb=1e9;neg=0;tot=0;mx=0
    for t in range(int(sys.argv[1])):
        edges=[(a,b) for a in range(n) for b in range(a+1,n) if rng.random()<0.75] or [(0,1)]
        J=rng.uniform(0.02,1.8,len(edges))
        c=rng.uniform(0,2,n)*(rng.random(n)<.8)
        c[:3]=1 if rng.random()<.5 else rng.uniform(0.05,2,3)
        H=10**rng.uniform(-1.5,0.7)
        Sv,truth=Sspin(n,edges,J,c,H)
        # need wv>0 for tanh; guard zeros
        wv=np.maximum(H*c,1e-14)
        t1,t2=decomp(n,edges,J,wv,bulk_configs(n,edges,J))
        err=abs(truth-(t1+t2)); worst=max(worst,err)
        tot+=1; neg+=(t2<-1e-13); minb=min(minb,t2); 
    print("n",n,"trials",tot,"max rel err of decomposition",worst,"bulk cov min",minb,"negatives",neg)
