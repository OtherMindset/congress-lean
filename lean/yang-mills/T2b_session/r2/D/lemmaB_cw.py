# End-to-end numerical test of theta-1 Lemma B on Curie-Weiss phi^4 (a plays role of mu).
import sys; sys.path.insert(0,'/home/claude/t2b/theta1')
import numpy as np
from cw_theta import site, obs
b,J,N=float(sys.argv[1]),float(sys.argv[2]),int(sys.argv[3]); a0=float(sys.argv[4]); th=float(sys.argv[5]); s0=float(sys.argv[6])
W=J*6+4
def O(a,h): return obs(site(a,b,W+2),J,N,h,W)
chi0=O(a0,1e-8)[1]; hmax=3*s0/chi0
# pass 1: estimate C on a box a in [a0-Da, a0]
Da=float(sys.argv[7]) if len(sys.argv)>7 else 0.3
C=0; 
for a in np.linspace(a0-Da,a0,7):
    S=site(a,b,W+2)
    for h in np.exp(np.linspace(np.log(hmax*1e-4),np.log(hmax),40)):
        m,chi,dam,_,_=obs(S,J,N,h,W)
        if m<=s0 and m>1e-4: C=max(C,(m-h*chi)/(m**th*dam))
print(f"b={b} J={J} N={N} a0={a0} chi0={chi0:.4g} hmax={hmax:.3g} C_needed(theta={th})={C:.4g}")
for Sfrac in [1.0,0.5,0.25]:
    Sv=s0*Sfrac; shift=C*Sv**th/th
    if shift>Da: print("  shift",shift,"exceeds box; skip"); continue
    ap=a0-shift*1.001; hp=2.01*Sv/chi0
    m=O(ap,hp)[0]
    print(f"  S={Sv:.3g}: a'={ap:.4f} h'={hp:.3g} m(a',h')={m:.4g} >= S? {m>=Sv}   (m(a0,h')={O(a0,hp)[0]:.4g})")
