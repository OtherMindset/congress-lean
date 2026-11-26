import numpy as np, sys
sys.path.insert(0,'/home/claude/t2b/theta1')
from cw_theta import site, obs
def m_of(a,b,J,N,h):
    W=J*6+4; S=site(a,b,W+2); return obs(S,J,N,h,W)[0]
def d2(a,b,J,N,hs,d=0.01):
    ms=np.array([[m_of(a+k*d,b,J,N,h) for h in hs] for k in (-2,-1,0,1,2)])
    return (-ms[0]+16*ms[1]-30*ms[2]+16*ms[3]-ms[4])/(12*d*d), (ms[0]-8*ms[1]+8*ms[3]-ms[4])/(12*d), ms[2]
hs=np.exp(np.linspace(np.log(1e-6),np.log(1.0),24))
for (a,b,J) in [(1.9,0.02,4.0),(1.5,0.1,4.0),(0.0,0.5,4.0),(1.0,0.1,2.0)]:
    for N in [64,256,1024]:
        k,s1,m=d2(a,b,J,N,hs)
        i=np.argmin(k/np.abs(s1)); neg=(k<0)
        print(f'a={a} b={b} J={J} N={N}: #h with kappa/N<0: {neg.sum()}/{len(hs)}; worst kappa/N={k.min():.4g} at h={hs[np.argmin(k)]:.3g}, m={m[np.argmin(k)]:.3f}; worst ratio kappa/|dm/da|={ (k/np.abs(s1)).min():.3g}; max kappa={k.max():.3g}',flush=True)
