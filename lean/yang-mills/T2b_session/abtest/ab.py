import numpy as np, itertools, sys, time
def getL(a,b,J,h,n):
    degJ=np.zeros(n)
    for (i,j),w in J.items(): degJ[i]+=w/2;degJ[j]+=w/2
    q=np.linspace(0,60,60001); L=0
    for i in range(n):
        e=-(a[i]-degJ[i])*q**2-b/2*q**4+h*q*1.0
        # include field boost generously: coupling to neighbours' magnitude bounded by quadratic part
        m=e.max(); idx=np.where(e>m-55)[0].max(); L=max(L,q[idx])
    return L
def moments(a,b,J,h,n,N):
    L=getL(a,b,J,h,n); q=np.linspace(-L,L,N); dq=q[1]-q[0]
    shape=lambda i:[N if k==i else 1 for k in range(n)]
    E=0
    qs=[q.reshape(shape(i)) for i in range(n)]
    for i in range(n): E=E+(-a[i]*qs[i]**2-b/2*qs[i]**4+h*qs[i])
    for (i,j),w in J.items(): E=E+w*qs[i]*qs[j]
    W=np.exp(E-E.max()); w0=W*qs[0]
    s=w0.sum(); 
    M1=[w0.sum(axis=tuple(k for k in range(n) if k!=i)) for i in range(n)]
    M2={}
    for i in range(n):
        for j in range(i+1,n):
            M2[(i,j)]=w0.sum(axis=tuple(k for k in range(n) if k not in (i,j)))
    # normalise by s: expectations under q0*mu: <F>_s := sum w0 F / s, then <q0 F>=<F>_s*<q0>... ratios invariant: use signed measure
    m0=s
    def E1(y,f): return (M1[y]*f(q)).sum()/s    # E_s[f(q_y)] = <q0 f>/<q0>
    def E2(x,y,fx,fy):
        i,j=min(x,y),max(x,y)
        A=M2[(i,j)]
        if x<y: return (A*np.outer(fx(q),fy(q))).sum()/s
        return (A*np.outer(fy(q),fx(q))).sum()/s
    sq=lambda z:z**2; id_=lambda z:z; one=lambda z:np.ones_like(z)
    # A: <q0 qx² qy²>/<q0> >= <q0qx²>/<q0> * <q0qy²>/<q0>
    Am=[]
    for x in range(n):
        for y in range(x+1,n):
            lhs=E2(x,y,sq,sq); rhs=E1(x,sq)*E1(y,sq)
            Am.append(((x,y),(lhs-rhs)/lhs))
    # B: <q0 qy² Q>/<q0> - <q0qy²>/<q0> <q0 Q>/<q0>
    EQ=sum(E1(z,id_) for z in range(n))
    Bm=[]
    for y in range(n):
        t=0
        for z in range(n):
            t+= E1(y,lambda u:u**3) if z==y else E2(y,z,sq,id_)
        d=t-E1(y,sq)*EQ
        Bm.append((y,d/abs(t)))
    return Am,Bm,L,E1(0,sq)
def rand_inst(rng,n,kind):
    a=rng.uniform(-2,3,n); b=rng.uniform(0.05,2) if rng.random()<.5 else 10**rng.uniform(np.log10(.05),np.log10(2)); h=10**rng.uniform(np.log10(.02),np.log10(3))
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    if kind=='complete': es=pairs
    elif kind=='ring': es=[(i,(i+1)%n) if i<(i+1)%n else ((i+1)%n,i) for i in range(n)]
    elif kind=='path': es=[(i,i+1) for i in range(n-1)]
    elif kind=='star': es=[(0,i) for i in range(1,n)]
    else:
        es=[p for p in pairs if rng.random()<.6] or [(0,1)]
    # site 0 random relabel via permutation of edges
    perm=rng.permutation(n); es=[tuple(sorted((perm[i],perm[j]))) for i,j in es]
    J={e:(rng.uniform(.1,2) if rng.random()<.5 else 10**rng.uniform(-1,np.log10(2))) for e in set(es)}
    return a,b,J,h
if __name__=="__main__":
    n=int(sys.argv[1]);T=int(sys.argv[2]);N1,N2=int(sys.argv[3]),int(sys.argv[4]);seed=int(sys.argv[5])
    rng=np.random.default_rng(seed); t0=time.time()
    worstA=(1e9,None);worstB=(1e9,None);maxdisc=0;cnt=0;viol=[]
    kinds=['complete','ring','path','star','rand']
    for t in range(T):
        kind=kinds[t%5]
        a,b,J,h=rand_inst(rng,n,kind)
        A1,B1,L,_=moments(a,b,J,h,n,N1); A2,B2,_,_=moments(a,b,J,h,n,N2)
        cnt+=1
        for (k,v1),(k2,v2) in zip(A1,A2):
            maxdisc=max(maxdisc,abs(v1-v2))
            if v2<worstA[0]: worstA=(v2,(kind,k,a.round(3).tolist(),round(b,3),{e:round(x,3) for e,x in J.items()},round(h,3),v1,v2,L))
        for (k,v1),(k2,v2) in zip(B1,B2):
            maxdisc=max(maxdisc,abs(v1-v2))
            if v2<worstB[0]: worstB=(v2,(kind,k,a.round(3).tolist(),round(b,3),{e:round(x,3) for e,x in J.items()},round(h,3),v1,v2,L))
        if min(v for _,v in A2)<-1e-8 or min(v for _,v in B2)<-1e-8: viol.append((kind,a.round(3).tolist(),b,J,h))
        if time.time()-t0>float(sys.argv[6]): break
    print("n",n,"trials",cnt,"time",round(time.time()-t0),"max |res1-res2| of rel margins",maxdisc)
    print("worst A (rel margin):",worstA); print("worst B (rel margin):",worstB); print("viol count",len(viol))
