import numpy as np, ab
orig=ab.getL
a=np.array([2.868,-1.723,2.383]);b=0.118;J={(0,2):1.172,(1,2):0.214};h=0.08
for s,N in [(1,91),(1,141),(1.6,201)]:
    ab.getL=lambda *x,s=s:orig(*x)*s
    A,B,L,_=ab.moments(a,b,J,h,3,N); print(s,N,round(L,2),B)
