import json, numpy as np, sys, glob
def load(fn):
    d=json.load(open(fn)); a=np.array(sorted(float(k) for k in d)); 
    m2=np.array([d[str(x)] ['m2b'] if str(x) in d else d[repr(x)]['m2b'] for x in a]); m4=np.array([d[str(x)]['m4b'] if str(x) in d else d[repr(x)]['m4b'] for x in a])
    return a,m2,m4
def kmin(a,m2,m4,b):
    # m2,m4: arrays over a (means). returns kappa_min per a index and SC ratio
    out=[]
    lm=np.log(m2)
    for i in range(len(a)):
        tau=m4[i]/(3*m2[i])
        # find a'' with m2(a'')=tau by log-linear interpolation (m2 decreasing)
        j=np.where(m2[i:]<=tau)[0]
        if len(j)==0: out.append(np.nan); continue
        j=j[0]+i
        if j==i: out.append(0.0); continue
        t=(np.log(tau)-lm[j-1])/(lm[j]-lm[j-1]); ax=a[j-1]+t*(a[j]-a[j-1])
        out.append((ax-a[i])/(4*b*m2[i]))
    return np.array(out)
for fn in sorted(glob.glob('res_*.json')):
    b=float(fn.split('_b')[1].split('_')[0]); L=int(fn.split('_L')[1].split('.json')[0])
    a,m2b,m4b=load(fn); nb=m2b.shape[1]
    m2=m2b.mean(1); m4=m4b.mean(1)
    k=kmin(a,m2,m4,b)
    # jackknife
    ks=[]
    for r in range(nb):
        idx=[q for q in range(nb) if q!=r]
        ks.append(kmin(a,m2b[:,idx].mean(1),m4b[:,idx].mean(1),b))
    ks=np.array(ks); err=np.sqrt((nb-1)*np.nanvar(ks,axis=0))
    B=m4/m2**2-3
    print(fn, "N a-values",len(a))
    for i in range(len(a)):
        print("  a=%.4f m2=%.5f B=%+.3f  kappa_min=%.3f +- %.3f   SCbound(1-|B|/3)=%.3f"%(a[i],m2[i],B[i],k[i],err[i],1+B[i]/3))
