import numpy as np, ab
# override getL to scale
orig=ab.getL
for scale,N in [(1,111),(1.5,181),(2,241)]:
    ab.getL=lambda *x,s=scale:orig(*x)*s
    a=np.array([1.839,2.054,2.043]);b=0.162;J={(0,1):0.684,(0,2):1.007};h=0.031
    A,B,L,_=ab.moments(a,b,J,h,3,N)
    print("A inst",scale,N,round(L,2),A[2],)
    a=np.array([1.238,-1.853,1.439]);b=0.081;J={(0,2):0.54,(1,2):0.264};h=0.095
    A,B,L,_=ab.moments(a,b,J,h,3,N)
    print("B inst",scale,N,round(L,2),B)
