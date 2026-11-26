from b3 import *
import sys
f=lambda w:2*w/np.sinh(2*w)
# bulk enumeration with exact collapsed per-edge weights.
STK=[(0,0,False),(0,0,True),(1,0,True),(0,1,True),(1,1,True)]
def bulk_configs(n,edges,J):
    cw=[collapsed(j) for j in J]
    out=[]
    for combo in itertools.product(range(5),repeat=len(edges)):
        wt=1.0; d1=[0]*n;d2=[0]*n; par=list(range(n))
        def fd(x):
            while par[x]!=x: par[x]=par[par[x]];x=par[x]
            return x
        for e,s in enumerate(combo):
            key=STK[s]; wt*=cw[e][key]
            u,v=edges[e]
            if key[0]: d1[u]^=1;d1[v]^=1
            if key[1]: d2[u]^=1;d2[v]^=1
            if key[2]: par[fd(u)]=fd(v)
        out.append((wt,np.array(d1),np.array(d2),np.array([fd(x) for x in range(n)])))
    return out
def Wgh(a,b,w):
    c,s=np.cosh(w),np.sinh(w)
    return np.where(a+b==0,c*c,np.where(a+b==1,s*c,s*s))
def Kgh(a,b,w):  # E[n1+n2 | parities]
    e=lambda p:np.where(p==1,w/np.tanh(w),w*np.tanh(w))
    return e(a)+e(b)

def measures(n,edges,J,w,B,bc):
    """returns dict of (Zweight, E[K], E[sum_{O1uO2} f], E[sum_{O1} f], const) for N,D under readings"""
    wv=np.asarray(w)
    res={}
    def run(srcs,k,mode):
        # srcs: set of bulk vertices in A (n1 boundary) ; ghost in A iff odd count automatically
        A=np.zeros(n,int); 
        for x in srcs: A[x]^=1
        tot=0;EK=0;Ef12=0;Ef1=0;Econst=0
        for wt,d1,d2,cl in bc:
            a=(d1+A)%2; b=d2
            if mode=='D' :
                Wg=Wgh(a,b,wv); z=wt*Wg.prod(); kk=Kgh(a,b,wv).sum()
                f12=(f(wv)*(a+b)).sum(); f1=(f(wv)*a).sum(); cons=(2*wv*np.tanh(wv)).sum()
            else:
                C=(cl==cl[k]) if k is not None else None
                if mode=='Ntrue':
                    if ((a+b)[C]>0).any(): continue
                    Wg=np.where(C,1.0,Wgh(a,b,wv)); z=wt*Wg.prod()
                    kk=np.where(C,0,Kgh(a,b,wv)).sum()
                    f12=(f(wv)*(a+b)).sum(); f1=(f(wv)*a).sum()   # C sites have a=b=0
                    cons=(np.where(C,0,2*wv*np.tanh(wv))).sum()
                elif mode=='Nnaive':   # ghost-marginalised bulk measure with indicator C∩(O1∪O2)=∅
                    if ((a+b)[C]>0).any(): continue
                    Wg=Wgh(a,b,wv); z=wt*Wg.prod(); kk=Kgh(a,b,wv).sum()
                    f12=(f(wv)*(a+b)).sum(); f1=(f(wv)*a).sum(); cons=(2*wv*np.tanh(wv)).sum()
            tot+=z;EK+=z*kk;Ef12+=z*f12;Ef1+=z*f1;Econst+=z*cons
        return tot,EK,Ef12,Ef1,Econst
    out={}
    for mode in ('Ntrue','Nnaive'):
        T=np.zeros(5)
        for k in B:
            for i in B:
                for j in B:
                    if i>=j: continue
                    # A={k,g} Delta {i,j}; bulk part
                    bulk=set([k])^set([i,j])
                    T+=np.array(run(bulk,k,mode))
        out[mode]=T
    T=np.zeros(5)
    for l in B: T+=np.array(run({l},None,'D'))
    out['D']=T
    return out
def instance(n,pe=0.7,Bsize=None,uniformc=True):
    edges=[(a,b) for a in range(n) for b in range(a+1,n) if rng.random()<pe]
    if not edges: edges=[(0,1)]
    J=rng.uniform(0.05,1.5,len(edges))
    Bsize=Bsize or rng.integers(2,n+1)
    B=list(rng.choice(n,Bsize,replace=False))
    c=rng.uniform(0,2,n); c[B]=1.0
    H=rng.uniform(0.05,1.5)
    return edges,J,c,H,B
if __name__=="__main__":
    ntr=int(sys.argv[1]); n=int(sys.argv[2])
    stats=dict(rel_true=0,rel_naive=0,rel_D=0,sgn_true=0,sgn_naive12=0,sgn_naive1=0,sgn_cor=0,N=0)
    worst_ratio=[]
    for t in range(ntr):
        edges,J,c,H,B=instance(n)
        S_,dlogS,S,w=spin_IC(n,edges,J,c,H,B)
        wv=H*c
        bc=bulk_configs(n,edges,J)
        o=measures(n,edges,J,wv,B,bc)
        Nt,Nn,D=o['Ntrue'],o['Nnaive'],o['D']
        # S from currents: ratio of totals (/Z0^2 common factor handled: ghost Z0 not in totals) -> compare via Z normalisation
        KN=Nt[1]/Nt[0]; KD=D[1]/D[0]
        # check H dlogS = KN-KD   (identity)
        stats['rel_true']=max(stats['rel_true'],abs(H*dlogS-(KN-KD)))
        # naive reduced claim: E_N[sum_O f]-E_D[sum_O f] , O=O1 u O2 (ghost-odd of both) ; and O1 only
        for tag,idx in (('12',2),('1',3)):
            dN=Nn[idx]/Nn[0]-D[idx]/D[0]
        d12=Nn[2]/Nn[0]-D[2]/D[0]; d1=Nn[3]/Nn[0]-D[3]/D[0]
        # corrected: full (const + f) with true N
        dcor=(Nt[2]/Nt[0]-D[2]/D[0])+(Nt[4]/Nt[0]-D[4]/D[0])
        stats['rel_naive']=max(stats['rel_naive'],abs(H*dlogS-d12))
        stats['rel_D']=max(stats['rel_D'],abs(H*dlogS-dcor))
        s=np.sign(dlogS)
        stats['sgn_naive12']+= (np.sign(d12)!=s); stats['sgn_naive1']+=(np.sign(d1)!=s); stats['sgn_cor']+=(np.sign(dcor)!=s)
        stats['N']+=1
        if t<4: print("inst",n,len(edges),"H dlogS=%.6e KN-KD=%.6e  naive(12)=%.6e naive(1)=%.6e corrected=%.6e"%(H*dlogS,KN-KD,d12,d1,dcor))
    print(stats)
