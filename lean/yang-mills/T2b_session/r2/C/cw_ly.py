# Lee-Yang zeros of CW phi^4 torus: Z(i eta)/Z(0) = E_w[cos(N eta w/J)] * exp(N eta^2/(2J)) ; zeros beta_j = N*eta_j.
import numpy as np, sys
sys.path.insert(0,'/home/claude/t2b/theta1')
from cw_theta import site
from scipy.optimize import brentq
def law(a,b,J,N):
    W=J*6+4; g,_,_,_=site(a,b,W+2)
    w=np.linspace(-W,W,200001); lw=-N*w**2/(2*J)+N*g(w); lw-=lw.max(); P=np.exp(lw); P/=P.sum()
    return w,P
def zeros(a,b,J,N,nz=6,bmax=60):
    w,P=law(a,b,J,N)
    f=lambda beta: (P*np.cos(beta*w/J)).sum()     # beta = N eta
    bs=np.linspace(0.01,bmax,6000); v=np.array([f(x) for x in bs])
    out=[]
    for i in range(len(bs)-1):
        if v[i]*v[i+1]<0: out.append(brentq(f,bs[i],bs[i+1],xtol=1e-12))
        if len(out)>=nz: break
    k2=(P*w**2).sum(); M2=k2/J**2-1/(N*J)
    return np.array(out),M2
if __name__=="__main__":
    b,J=float(sys.argv[1]),float(sys.argv[2]); avals=[float(x) for x in sys.argv[3].split(',')]
    da=1e-3
    for N in [16,64,256,1024]:
        for a in avals:
            z0,M2=zeros(a,b,J,N); zp,M2p=zeros(a+da,b,J,N); zm,M2m=zeros(a-da,b,J,N)
            n=min(len(z0),len(zp),len(zm))
            if n==0: print(N,a,"no zeros in range"); continue
            dlog=(np.log(zp[:n]**2)-np.log(zm[:n]**2))/(2*da)   # d_a log beta_j^2
            print(f"N={N:5d} a={a}: M_N={np.sqrt(M2):.4f} beta_j*M_N=",np.round(z0[:4]*np.sqrt(M2),3)," d_a log beta_j^2=",np.round(dlog[:4],4),
                  f" -d_a(beta1^-2)={-(zp[0]**-2-zm[0]**-2)/(2*da):.4f} -d_aM2={-(M2p-M2m)/(2*da):.4f} 2sum1/beta^2(6)={2*(z0**-2.).sum():.4f}",flush=True)
