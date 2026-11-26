import numpy as np, sys, ab, collections
n=int(sys.argv[1]);T=int(sys.argv[2]);N=int(sys.argv[3]);seed=int(sys.argv[4])
rng=np.random.default_rng(seed)
cA=collections.Counter();cB=collections.Counter();totA=collections.Counter();totB=collections.Counter()
worstA=0;worstB=0;exA=exB=None;homA=0;homB=0
import time;t0=time.time()
for t in range(T):
    kind=['complete','ring','path','star','rand'][t%5]
    a,b,J,h=ab.rand_inst(rng,n,kind)
    if t%4==3: a[:]=a[0]       # homogeneous a
    A,B,L,_=ab.moments(a,b,J,h,n,N)
    hom=(t%4==3)
    nb=lambda x,y:tuple(sorted((x,y))) in J
    for (x,y),v in A:
        typ='A:0in' if 0 in (x,y) else ('A:both nbrs of 0' if nb(0,x) and nb(0,y) else 'A:other')
        totA[(typ,hom)]+=1
        if v<-1e-9: cA[(typ,hom)]+=1
        if v<worstA: worstA=v;exA=(kind,(x,y),a.round(3).tolist(),round(b,3),{e:round(x_,3) for e,x_ in J.items()},round(h,3),v)
    for y,v in B:
        typ='B:y=0' if y==0 else ('B:y nbr of 0' if nb(0,y) else 'B:y non-nbr')
        totB[(typ,hom)]+=1
        if v<-1e-9: cB[(typ,hom)]+=1
        if v<worstB: worstB=v;exB=(kind,y,a.round(3).tolist(),round(b,3),{e:round(x_,3) for e,x_ in J.items()},round(h,3),v)
    if time.time()-t0>float(sys.argv[5]):break
print("trials",t+1)
for k in sorted(totA): print(k,"viol",cA[k],"/",totA[k])
for k in sorted(totB): print(k,"viol",cB[k],"/",totB[k])
print("worstA",worstA,exA);print("worstB",worstB,exB)
