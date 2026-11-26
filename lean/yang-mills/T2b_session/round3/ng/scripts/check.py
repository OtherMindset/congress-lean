"""(1) one-site check of the pairing identity |B| = 3 E_{w x w}[1-R], i.e. <phi^4> = 3 int int Z(t1+t2)/Z dt1 dt2,
    and <phi^2> = int Z(t)/Z dt;  (2) tree-bound necessity |B_L| <= 24 b chi^2 / N on all MC Binder scans."""
import numpy as np, json, glob
from scipy import integrate
def Zt(t,a,b):
    f=lambda p: np.exp(-a*p*p-b*p**4-2*a*t-4*b*t*t-4*b*t*p*p)
    return integrate.quad(f,-np.inf,np.inf,limit=200)[0]
for a,b in [(1.0,0.5),(-2.0,0.3),(-6.0,1.0),(0.5,0.01)]:
    Z=Zt(0,a,b)
    m2=integrate.quad(lambda p:p*p*np.exp(-a*p*p-b*p**4),-np.inf,np.inf)[0]/Z
    m4=integrate.quad(lambda p:p**4*np.exp(-a*p*p-b*p**4),-np.inf,np.inf)[0]/Z
    w2=integrate.quad(lambda t:Zt(t,a,b),0,np.inf,limit=200)[0]/Z
    w4=3*integrate.quad(lambda u:u*Zt(u,a,b),0,np.inf,limit=200)[0]/Z   # int int Z(t1+t2) = int u Z(u) du
    print(f"a={a:5} b={b:5}: m2={m2:.8f} walk={w2:.8f} | m4={m4:.8f} walk={w4:.8f} | B={m4/m2**2-3:+.6f}  tree 24 b m2^2={24*b*m2**2:.4f}")
print("--- tree-bound necessity on MC Binder scans: |B| <= 24 b chi^2/N (lattice units)")
worst=0
for f in glob.glob('/home/claude/t2b/mc_eps/binder/scan_*.json'):
    b={'b008':0.08,'b002':0.02,'b0005':0.005,'b3':0.00125}[f.split('scan_')[1].split('_')[0]]
    for r in json.load(open(f)):
        B=3*r['U']; eB=3*r['eU']; bound=24*b*r['chi']**2/r['L']**2
        ratio=(B-2*eB)/bound; worst=max(worst,ratio)
        if bound<3: print(f"  b={b} a={r['a']} L={r['L']}: |B|={B:.3f}+-{eB:.3f}  bound={bound:.3f}  ratio={B/bound:.2f}")
print("max (|B|-2sigma)/bound =",round(worst,3))
