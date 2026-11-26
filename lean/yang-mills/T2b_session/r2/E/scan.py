import numpy as np, sys, json
from exact import run
rng=np.random.default_rng(int(sys.argv[2]))
n=int(sys.argv[1]); N=int(sys.argv[3]); ng={1:1500,2:300,3:70,4:36}[n]
rows=[]
for i in range(N):
    a=rng.uniform(-4,4); b=np.exp(rng.uniform(np.log(.02),np.log(2))); J=np.exp(rng.uniform(np.log(.1),np.log(3))); H=np.exp(rng.uniform(np.log(.01),np.log(3)))
    try: r=run(n,a,b,J,H,ng)
    except Exception as e: continue
    loc=min(v for k,v in r.items() if k not in('L','U'))
    rows.append((a,b,J,H,loc,r['U'],r['L']))
rows=np.array(rows)
np.save(f'scan{n}_{sys.argv[2]}.npy',rows)
print(n,len(rows),'frac loc<0',(rows[:,4]<0).mean(),'frac U<0',(rows[:,5]<0).mean(),'min loc',rows[:,4].min(),'min U',rows[:,5].min())
