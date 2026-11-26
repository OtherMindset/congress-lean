import numpy as np, mpmath as mp
mp.mp.dps=60
exec(open('ly1h.py').read().split('rng=')[0])
def logZ(blocks,H):
    s=0
    for typ,a,extra in blocks:
        if typ==0: s+=mp.log(mp.cosh(a*H))
        elif typ==1: s+=mp.log(mp.cosh(2*a*H)-mp.cos(extra))
        elif typ==2: s+=a*H**2
        else: s+=a**2*H**2/2+mp.log(1+a**2*H**2)
    return s
def Tmp(blocks,H):
    k=[mp.diff(lambda h: logZ(blocks,h),H,n) for n in range(1,5)]
    return 2*k[0]**2*k[2]+k[0]*k[3]-k[1]*k[2], k[2]
rng=np.random.default_rng(3); Hs=np.geomspace(1e-3,30,200)
found=0; checked=0
for trial in range(6000):
    k=[0*Hs]*4; blocks=[]
    for _ in range(rng.integers(1,5)):
        typ=int(rng.integers(4)); a=float(rng.exponential(1)*rng.choice([0.2,1,4])); th=float(rng.uniform(np.pi/2,np.pi))
        b=[blk_cosh(a,Hs),blk_trig(a,th,Hs),blk_gauss(a,Hs),blk_bad(a,Hs)][typ]
        blocks.append((typ,mp.mpf(a),mp.mpf(th))); k=[k[i]+b[i] for i in range(4)]
    k1,k2,k3,k4=k; T=2*k1**2*k3+k1*k4-k2*k3
    ghs=(k3<=1e-12*np.abs(k1)**3).all()
    sc=np.abs(2*k1**2*k3)+np.abs(k1*k4)+np.abs(k2*k3)+1e-300
    if not ghs: continue
    r=T/sc; i=np.nanargmax(r)
    if r[i]>1e-7:
        checked+=1
        # verify in mpmath at a grid near
        Hm=mp.mpf(Hs[i]); t,k3m=Tmp(blocks,Hm)
        # check GHS in mp along a few points
        if t>0:
            g=all(Tmp(blocks,mp.mpf(h))[1]<=0 for h in Hs[::20])
            if g: found+=1; print('GENUINE?',[(b[0],float(b[1])) for b in blocks],float(Hm),mp.nstr(t,8),flush=True)
        if checked>40: break
print('checked',checked,'genuine',found)
