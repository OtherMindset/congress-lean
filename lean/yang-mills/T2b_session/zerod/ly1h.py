import numpy as np
# log Z building blocks with analytic derivatives via complex-step-free finite approach: use exact formulas
def blk_cosh(a,H):
    t=np.tanh(a*H); S=1-t**2; return [a*t, a**2*S, -2*a**3*S*t, 2*a**4*S*(2*t**2-S)]
def blk_trig(a,th,H):  # log(cosh(2aH)-cos th), positive measure iff cos th<=0
    u=2*a*H; E=np.exp(-u); c=np.cos(th); den=1+E**2-2*c*E
    p=(1+E**2)/den; q=(1-E**2)/den
    f1=q; f2=p-q**2; f3=q-3*q*p+2*q**3; f4=p-3*p**2-4*q**2+12*q**2*p-6*q**4
    return [(2*a)*f1,(2*a)**2*f2,(2*a)**3*f3,(2*a)**4*f4]
def blk_gauss(b,H): return [2*b*H,2*b+0*H,0*H,0*H]
def blk_bad(s,H): # Z=e^{s^2H^2/2}(1+s^2H^2): x^2 e^{-x^2/2s^2}
    w=1/s**2+H**2; v=1/w; y=H**2*v
    return [H*(s**2+2*v), s**2+v*(2-4*y), H*v**2*(-12+16*y), v**2*(-12+96*y-96*y**2)]
rng=np.random.default_rng(3); Hs=np.geomspace(1e-3,30,400)
res={'GHS&T>0':0,'nonGHS&T>0':0,'GHS&ok':0,'nonGHS&ok':0}; ex=None
for trial in range(20000):
    k=[0*Hs]*4; blocks=[]
    for _ in range(rng.integers(1,5)):
        typ=rng.integers(4); a=rng.exponential(1)*rng.choice([0.2,1,4])
        if typ==0: b=blk_cosh(a,Hs)
        elif typ==1: th=rng.uniform(np.pi/2,np.pi); b=blk_trig(a,th,Hs)
        elif typ==2: b=blk_gauss(a,Hs)
        else: b=blk_bad(a,Hs)
        blocks.append((typ,round(a,3))); k=[k[i]+b[i] for i in range(4)]
    k1,k2,k3,k4=k; T=2*k1**2*k3+k1*k4-k2*k3
    ghs=(k3<=1e-12*np.abs(k1)**3+1e-300).all(); sc=np.abs(2*k1**2*k3)+np.abs(k1*k4)+np.abs(k2*k3)+1e-300; ok=sc>1e-200
    if not ok.any(): continue
    bad=((T/sc)[ok]).max()>1e-7
    key=('GHS' if ghs else 'nonGHS')+('&T>0' if bad else '&ok'); res[key]+=1
    if ghs and bad and ex is None: ex=(blocks,((T/sc)[ok]).max(),Hs[ok][np.argmax((T/sc)[ok])])
print(res); print('example GHS but violating:',ex)
