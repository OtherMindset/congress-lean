# FD_kappa in the Ising limit b->inf of phi^4 (well phi^2=v, coupling J=1  =>  Ising at beta=v).
# FD_kappa  <=>  (1-2k f(beta)) f(beta(1-2k f(beta))) <= (1-|B(beta)|/3) f(beta),  f = <(M/N)^2>_Ising.
import numpy as np, sys
from scipy.optimize import brentq
def ising2d_moments(beta,L,K=40):
    n=2**L; s=np.arange(n)
    spins=1-2*((s[:,None]>>np.arange(L))&1)          # n x L
    Mrow=spins.sum(1)
    Erow=(spins*np.roll(spins,1,axis=1)).sum(1)       # horizontal bonds in row
    V=spins@spins.T                                   # vertical bonds between rows
    logT=beta*(V+0.5*Erow[:,None]+0.5*Erow[None,:])
    T=np.exp(logT-logT.max())
    ev0=np.linalg.eigvalsh(T); lm=ev0.max()
    Z0=((ev0/lm)**L).sum()
    N=L*L
    # rough scale
    f0=None
    def Zh(h):
        D=np.exp(0.5*h*Mrow)
        ev=np.linalg.eigvals((D[:,None]*T*D[None,:])/lm)
        return (ev**L).sum()/Z0
    # scale r ~ 1/sqrt(<M^2>) ; get <M^2> from small real h
    hh=1e-3; M2g=2*(Zh(hh).real-1)/hh**2
    r=1/np.sqrt(M2g)
    th=2*np.pi*np.arange(K)/K
    vals=np.array([Zh(r*np.exp(1j*t)) for t in th])
    c=np.fft.fft(vals)/K
    M2=2*(c[2]/r**2).real; M4=24*(c[4]/r**4).real
    return M2/N**2, M4/M2**2-3
def ising1d(beta,N):
    t=np.tanh(beta)
    # <s0 sx> on ring = (t^x + t^(N-x))/(1+t^N)
    x=np.arange(N); G=(t**x+t**(N-x))/(1+t**N)
    return G.sum()/N
def fd_kmin(f,B,fun,beta):
    tgt=(1-abs(B)/3)*f
    def g(k):
        r=1-2*k*f
        if r<=0: return -tgt
        return r*fun(beta*r)-tgt
    if g(1e-9)<=0: return 0.0
    hi=0.5/f  # at this k, r=0 -> g<0
    return brentq(g,1e-9,hi,xtol=1e-7)
if __name__=="__main__":
    print("# 2D Ising torus LxL, Ising limit of phi^4.  beta, f=m2, B, kappa_min")
    for L in [4,6,8,10]:
        worst=0; row=[]
        for beta in [0.05,0.1,0.2,0.3,0.35,0.4,0.42,0.44,0.46,0.5,0.6,0.8]:
            f,B=ising2d_moments(beta,L)
            fun=lambda bb: ising2d_moments(bb,L)[0]
            k=fd_kmin(f,B,fun,beta)
            worst=max(worst,k); row.append("%.2f:%.3f(B%.2f)"%(beta,k,B))
        print("L=%d worst=%.4f"%(L,worst)); print("   "," ".join(row)); sys.stdout.flush()
