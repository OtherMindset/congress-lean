import numpy as np,sys; sys.path.insert(0,'.')
from cw import *
a,b,J=1.0,1.0,5.0
for N in [16,64]:
    ys=np.linspace(-1.5,1.5,301); dy=ys[1]-ys[0]
    C=cond(N,ys,a,b)
    lp=C[:,0]+J*N*ys**2/2   # log density of Y=M/N (up to const)
    # EOM check: -dlogp/dv = -J y + 2a y + 4b tau3
    dl=np.gradient(lp,dy)/N
    res=-dl-(-J*ys+2*a*ys+4*b*C[:,2])
    print(N,'EOM residual max',np.abs(res[5:-5]).max())
    np.save(f'cw_N{N}.npy',np.c_[ys,lp,C[:,1],C[:,2]])
