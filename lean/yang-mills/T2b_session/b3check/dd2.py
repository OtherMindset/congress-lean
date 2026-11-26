from decomp import *
n=4;neg=[];tot=0;mn=0
for t in range(500):
    edges=[(a,b) for a in range(n) for b in range(a+1,n) if rng.random()<0.75] or [(0,1)]
    J=rng.uniform(0.02,1.8,len(edges)); c=rng.uniform(0,2,n)*(rng.random(n)<.8)
    c[:3]=1 if rng.random()<.5 else rng.uniform(0.05,2,3)
    H=10**rng.uniform(-1.5,0.7)
    Sv,truth=Sspin(n,edges,J,c,H); wv=np.maximum(H*c,1e-14)
    t1,t2=decomp(n,edges,J,wv,bulk_configs(n,edges,J)); tot+=1
    if t2<-1e-12: neg.append((t2,t1,truth,edges,J.round(4).tolist(),c.round(4).tolist(),H))
print(tot,len(neg))
for x in sorted(neg,key=lambda z:z[0])[:3]: print(x)
