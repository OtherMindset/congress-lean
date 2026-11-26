import numpy as np
def R(vals,wts,H):
    lw=H*vals; w=wts*np.exp(lw-lw.max()); w/=w.sum()
    m1,m2,m3=[(w*vals**k).sum() for k in (1,2,3)]; return (m3-m1*m2)/m1
Hs=np.linspace(1e-3,4,4000)
for c in [0,0.5,1,2,2.9,3,3.1,3.5,5,10,30]:
    vals=np.array([-3,-1,1,3.]); wts=np.array([1,c,c,1.])
    Rs=np.array([R(vals,wts,H) for H in Hs]); d=np.diff(Rs)
    print('c=%5.2f LY=%s  max dR=%.3e at H=%.3f  R(0)=%.4f'%(c,0<=c<=3,d.max(),Hs[d.argmax()],Rs[0]))
