import numpy as np
def cums(vals,wts,H):
    lw=H*vals; w=wts*np.exp(lw-lw.max()); w/=w.sum()
    m=[(w*vals**k).sum() for k in range(5)]
    k1=m[1]; k2=m[2]-m[1]**2; k3=m[3]-3*m[2]*m[1]+2*m[1]**3
    k4=m[4]-4*m[3]*m[1]-3*m[2]**2+12*m[2]*m[1]**2-6*m[1]**4
    return k1,k2,k3,k4
Hs=np.linspace(1e-3,5,3000)
for c in [0.5,1,2,3,4,5,6,7,8,9,10,15,30]:
    vals=np.array([-3,-1,1,3.]); wts=np.array([1,c,c,1.])
    K=np.array([cums(vals,wts,H) for H in Hs]); k1,k2,k3,k4=K.T
    T=2*k1**2*k3+k1*k4-k2*k3
    print('c=%5.1f LY=%d GHS(k3<=0)=%d  R-monotone(T<=0)=%d'%(c,c<=3,k3.max()<=1e-12,T.max()<=1e-12))
