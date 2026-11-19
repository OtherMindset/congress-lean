from fractions import Fraction as Fr
P=60; D=1<<P
def dn(x):
    x=Fr(x); return Fr((x.numerator<<P)//x.denominator, D)
def up(x):
    x=Fr(x); return Fr(-((-x.numerator<<P)//x.denominator), D)
PAD=int(D*Fr(1,10**13))
def _fl(x): x=Fr(x); return (x.numerator*D)//x.denominator
def _ce(x): x=Fr(x); return -((-x.numerator*D)//x.denominator)
class I:
    __slots__=('l','h')
    def __init__(s,lo,hi=None,raw=False):
        if raw: s.l=lo; s.h=hi
        else:
            s.l=_fl(lo); s.h=_ce(lo if hi is None else hi)
    @property
    def lo(s): return Fr(s.l,D)
    @property
    def hi(s): return Fr(s.h,D)
    def __add__(s,o):
        o=o if isinstance(o,I) else I(o); return I(s.l+o.l,s.h+o.h,True)
    __radd__=__add__
    def __sub__(s,o):
        o=o if isinstance(o,I) else I(o); return I(s.l-o.h,s.h-o.l,True)
    def __rsub__(s,o): return I(o)-s
    def __mul__(s,o):
        o=o if isinstance(o,I) else I(o)
        p=(s.l*o.l,s.l*o.h,s.h*o.l,s.h*o.h); return I(min(p)>>P,-((-max(p))>>P),True)
    __rmul__=__mul__
    def __neg__(s): return I(-s.h,-s.l,True)
def recip(x):
    assert x.l>0; return I((D*D)//x.h,-((-D*D)//x.l),True)
TAIL=Fr(1,10**14)
FACT=[1]
for k in range(1,60): FACT.append(FACT[-1]*k)
def _exp_int(xi):  # xi int scaled; returns int approx of e^x*D (error << PAD)
    t=D; s=D
    for k in range(1,19):
        t=(t*xi//D)//k; s+=t
    return s
def iexp(w):
    # (assert added at second pass by route lead A, Claude Opus 5.5)
    assert max(-w.l,w.h)<=3*D//2
    return I(_exp_int(w.l)-PAD,_exp_int(w.h)+PAD,True)
SN=14
_CS={}
def _coef(m,d):
    c=1
    for j in range(d): c*=(m-j)
    return (c*D)//FACT[2*m+1]
def _S_int(zi,d):
    s=0; pw=D
    for m in range(d,SN):
        s+=_coef(m,d)*pw//D; pw=pw*zi//D
    return s
def iS(z,d):
    assert z.l>=0
    return I(_S_int(z.l,d)-PAD,_S_int(z.h,d)+PAD,True)
# jets: (v,d1,d2) of I
def jmul(f,g): return (f[0]*g[0], f[1]*g[0]+f[0]*g[1], f[2]*g[0]+2*f[1]*g[1]+f[0]*g[2])
def jadd(f,g): return (f[0]+g[0],f[1]+g[1],f[2]+g[2])
def jrecip(f):
    r=recip(f[0]); r2=r*r
    return (r, -(f[1]*r2), -(f[2]*r2)+2*(f[1]*f[1])*(r2*r))
def jc(c): return (I(c),I(0),I(0))
def jscale(f,c): return (f[0]*c,f[1]*c,f[2]*c)
def jexp(w):
    e=iexp(w[0]); return (e, e*w[1], e*(w[2]+w[1]*w[1]))
def jS(z,d=0):
    s0=iS(z[0],d); s1=iS(z[0],d+1); s2=iS(z[0],d+2)
    return (s0, s1*z[1], s2*(z[1]*z[1])+s1*z[2])
def integrand(s,Ka,Kb2,deriv=False,Ai=None,Kb2d=None):
    """jets of f0=4*y/(1+s^2)*exp(K*Aa*u)*S(K^2 (1-a^2) y), and f1=u*f0 ; s: I interval"""
    sj=(s,I(1),I(0)); s2=jmul(sj,sj); den=jadd(jc(1),s2); rd=jrecip(den)
    u=jscale(jmul(sj,rd),2); nu=jmul(jadd(jc(1),jscale(s2,-1)),rd); y=jmul(nu,nu)
    w=jscale(u,Ka); z=jscale(y,Kb2)
    ye=jmul(jmul(y,rd),jexp(w))
    f0=jscale(jmul(ye,jS(z)),4)
    if not deriv: return f0,jmul(u,f0)
    g=jmul(f0,jscale(u,Ai))
    g=jadd(g,jscale(jmul(jmul(ye,y),jS(z,1)),8*Kb2d))
    return g,jmul(u,g)

PI_LO=Fr(314159265,10**8); PI_HI=Fr(314159266,10**8)
def bes(k,N=16):
    """N,D partial sums for kappa=k rational: D=sum q^m/(m!(m+1)!), Nn=sum q^m/(m!(m+2)!), q=k^2/4. returns (Dlo,Dhi,Nlo,Nhi)"""
    q=Fr(k)**2/4; t=Fr(1); d=n=Fr(0)
    for m in range(N):
        d+=t/(FACT[m]*FACT[m+1]); n+=t/(FACT[m]*FACT[m+2]); t*=q
    tl=t/(FACT[N]*FACT[N+1])*2; tn=t/(FACT[N]*FACT[N+2])*2
    return d,d+tl,n,n+tn
def sqrt_s(c):  # s_c with 2s/(1+s^2)=c approx, rational
    c=Fr(c)
    if c==0: return Fr(0)
    from math import isqrt
    r=Fr(isqrt(int((1-c*c)*10**24)),10**12)   # approx sqrt(1-c^2)
    s=(1-r)/c
    return Fr(round(s*10**6),10**6)
def prep(k1,k2,a1,a2):
    k1,k2,a1,a2=map(Fr,(k1,k2,a1,a2))
    K=I(k1,k2); Ai=I(a1,a2)
    d1=bes(k1); d2=bes(k2)
    Alo=(k1/2)*d1[2]/d1[1] if k1>0 else Fr(0)
    Ahi=(k2/2)*d2[3]/d2[0]
    u0=Ai*I(dn(Alo),up(Ahi))
    cc=(u0.lo+u0.hi)/2
    sc=sqrt_s(cc); c=2*sc/(1+sc*sc)
    w=max(abs(u0.lo-c),abs(u0.hi-c))
    Ka=K*Ai; Kb2=K*K*(Fr(1)-Ai*Ai); Kb2d=K*(Fr(1)-Ai*Ai)
    return dict(K=K,Ai=Ai,d1=d1,d2=d2,Alo=Alo,Ahi=Ahi,u0=u0,sc=sc,c=c,w=w,Ka=Ka,Kb2=Kb2,Kb2d=Kb2d)
def quad(p,sa,sb,n,B,deriv):
    h=(sb-sa)/n; T0=I(0);T1=I(0); nodes=[]
    kw=dict(deriv=deriv,Ai=p['Ai'],Kb2d=p['Kb2d'])
    for j in range(n+1):
        f0,f1=integrand(I(sa+h*j),p['Ka'],p['Kb2'],**kw); nodes.append((f0[0],f1[0]))
    for j in range(n):
        T0=T0+(nodes[j][0]+nodes[j+1][0])*(h/2); T1=T1+(nodes[j][1]+nodes[j+1][1])*(h/2)
    for j0 in range(0,n,B):
        j1=min(n,j0+B)
        f0,f1=integrand(I(sa+h*j0,sa+h*j1),p['Ka'],p['Kb2'],**kw)
        L=(j1-j0)*h**3/12
        T0=I(T0.lo-up(L*max(f0[2].hi,0)),T0.hi+up(L*max(-f0[2].lo,0)))
        T1=I(T1.lo-up(L*max(f1[2].hi,0)),T1.hi+up(L*max(-f1[2].lo,0)))
    return T0,T1
def mbox(k1,k2,a1,a2,n,B):
    """upper bound of M over kappa in [k1,k2] x a in [a1,a2] by interval wrapping (use mostly with k1=k2,a1=a2), plus lower bound"""
    p=prep(k1,k2,a1,a2)
    T0,T1=quad(p,p['sc'],1,n,B,False)
    Q=(T1-p['u0']*T0)*2+I(-6*p['w']**2,6*p['w']**2)
    Zlo=PI_LO*p['d1'][0]; Zhi=PI_HI*p['d2'][1]
    return up(Q.hi/Zlo), dn(max(Q.lo,0)/Zhi)
def dM_up(k1,k2,a,n=40,B=8):
    """rigorous upper bound for sup_{k in [k1,k2]} dM/dk at fixed a"""
    p=prep(k1,k2,a,a); sc=p['sc']; u0=p['u0']; w=p['w']
    F0p,F1p=quad(p,sc,1,n,B,False); F0m,F1m=quad(p,-1,sc,n,B,False)
    G0p,G1p=quad(p,sc,1,n,B,True); G0m,G1m=quad(p,-1,sc,n,B,True)
    Q=(G1p-u0*G0p)-(G1m-u0*G0m)+I(-12*w*w,12*w*w)
    Pm=(F0p-F0m)+I(-10*w,10*w)
    Zlo=PI_LO*p['d1'][0]; Zhi=PI_HI*p['d2'][1]
    # M interval: from one-sided formula
    Mnum=(F1p-u0*F0p)*2+I(-6*w*w,6*w*w)
    Mlo=max(Mnum.lo,Fr(0))/Zhi; Mhi=Mnum.hi/Zlo
    # A' <= 1-3*rho, rho=(1/2)N/D at k2 (A/k decreasing)
    d2=p['d2']; rho=Fr(1,2)*d2[2]/d2[1]
    Apr=I(0,max(Fr(0),1-3*rho))
    u0p=Apr*I(a,a)
    t1=Q.hi/Zlo if Q.hi>=0 else Q.hi/Zhi
    # (u0' * Pm)/Z, upper bound of -(.) : need min of u0p*Pm
    cand=[u0p.lo*Pm.lo,u0p.lo*Pm.hi,u0p.hi*Pm.lo,u0p.hi*Pm.hi]
    mn=min(cand); t2=(-mn)/Zlo if -mn>=0 else (-mn)/Zhi
    t3=Mlo*p['Alo']
    return up(t1+t2-t3)

def dec(x):
    v=-((-x.numerator*10**9)//x.denominator); return "%d.%09d"%(v//10**9,v%10**9)
def agrid(N):
    pts=[]
    for j in range(N+1):
        t=Fr(j,N); a=(1-t*t)/(1+t*t); b=2*t/(1+t*t); pts.append((a,b))
    return pts
def cfac(p,q):
    d=p[0]*q[0]+p[1]*q[1]; return (1+2/(1+d))/2
def run(kA,kB,eps,NPT=120,NDV=40,levels=(16,32,64),dmax=Fr(1,8),verbose=True):
    T=Fr(4)/(3*PI_HI)+eps
    k1=Fr(kA); out=[]; mx=Fr(0); evals=0
    cacheM={}
    while k1<kB:
        d=min(dmax,Fr(kB)-k1); ok=False
        while not ok:
            k2=k1+d
            for lev in levels:
                pts=agrid(lev); Ms=[]
                for j,(a,b) in enumerate(pts):
                    key=(k1,a)
                    if key not in cacheM: cacheM[key]=mbox(k1,k1,a,a,NPT,10)[0]
                    Ms.append(cacheM[key])
                if max(Ms)>T: continue
                Bs=[]
                for j,(a,b) in enumerate(pts):
                    if Ms[j]+ (0) <=T:
                        L=dM_up(k1,k2,a,NDV)
                        Bs.append(Ms[j]+max(L,Fr(0))*d)
                bound=max(cfac(pts[j],pts[j+1])*max(Bs[j],Bs[j+1]) for j in range(lev))
                if bound<=T:
                    ok=True; out.append((k1,k2,lev,bound)); mx=max(mx,bound); break
            if not ok:
                d=d/2
                if d<Fr(1,4096): raise SystemExit("FAIL at kappa=%s"%k1)
        if verbose: print("cell",k1,k2,"arcs",lev,"bound<=",dec(bound),flush=True)
        k1=k2
    return out,mx,T

KA,KB=Fr("9/16"),Fr("4/5")
print("computation 4: kappa in [%s, %s], all unit q (a in [0,1])"%(KA,KB))
out,mx,T=run(KA,KB,Fr(1,2000),NPT=250,NDV=50,levels=(32,64,128))
print("cells:",len(out))
print("max certified bound on M over this range <=",dec(mx))
print("target T = 4/(3*pi_hi)+1/2000 <=",dec(T),"; certified max<=T:",mx<=T)
print("CERTIFIED: sup M(kappa,q) over kappa in [%s,%s] is <= 4/(3 pi)+1/2000"%(KA,KB))
