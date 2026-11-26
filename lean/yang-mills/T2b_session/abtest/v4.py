import numpy as np, ab
a=np.array([2.601,2.92,1.365,-1.111]);b=1.69;J={(2,3):1.484,(0,2):0.665,(0,1):1.379};h=0.021
for N in (49,65,81):
    A,B,L,_=ab.moments(a,b,J,h,4,N); print(N,round(L,2),[x for x in A if x[0]==(1,2)],min(v for _,v in B))
