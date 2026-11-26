from b3 import *
import sys
# Identity 1: <s_k;s_i s_j> = <s_A> P[k not~ g]  = num/Z0^2 ;  num = sum Z^A Z^0 1[..]
for trial,(n,T) in enumerate([(2,10),(2,14),(2,14),(3,5)]):
    ed=[(a,b) for a in range(n) for b in range(a+1,n)]
    J=rng.uniform(0.1,1.0,len(ed)); c=rng.uniform(0.3,1.5,n); H=rng.uniform(0.2,0.8)
    wg=H*c
    S,w=spin_data(n,ed,J,c,H)
    for (k,i,j) in [(k,i,j) for k in range(n) for i in range(n) for j in range(i+1,n)][:6]:
        if n==3 and T>5: T=5
        num,ZA,Z0=trunc_check(n,ed,J,wg,T,k,i,j)
        lhs=cov(w,S[:,k].astype(float),(S[:,i]*S[:,j]).astype(float))
        print(n,T,(k,i,j),"spin %.12f  current %.12f  diff %.2e"%(lhs,num/Z0,lhs-num/Z0)); sys.stdout.flush()
