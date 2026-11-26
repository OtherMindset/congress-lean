import mpmath as mp
mp.mp.dps=40
def mom(V,H,n):
    f=lambda x: x**n*mp.e**(H*x-V(x))
    return mp.quad(f,[-mp.inf,-3,0,3,mp.inf])
def R(V,H):
    Z=mom(V,H,0);m1=mom(V,H,1)/Z;m2=mom(V,H,2)/Z;m3=mom(V,H,3)/Z
    return (m3-m1*m2)/m1
def Rpair(V,H):  # via pi_h representation: 2*E_pi[g]
    W=lambda q,t: V((q+t)/mp.sqrt(2))+V((q-t)/mp.sqrt(2))
    h=mp.sqrt(2)*H
    def g(q):
        a=mp.quad(lambda t:t**2*mp.e**(-W(q,t)),[-mp.inf,0,mp.inf]); b=mp.quad(lambda t:mp.e**(-W(q,t)),[-mp.inf,0,mp.inf]); return a/b
    rho=lambda q: mp.quad(lambda t:mp.e**(-W(q,t)),[-mp.inf,0,mp.inf])
    num=mp.quad(lambda q:g(q)*q*mp.sinh(h*q)*rho(q),[0,2,mp.inf]); den=mp.quad(lambda q:q*mp.sinh(h*q)*rho(q),[0,2,mp.inf])
    return 2*num/den
import sys
cases={'quartic a=1,b=1':lambda x:x**2+x**4,'quartic a=-3,b=1':lambda x:-3*x**2+x**4,
 'quartic a=-10,b=1':lambda x:-10*x**2+x**4,'phi6 a=-2':lambda x:-2*x**2+x**6/6,
 'cosh-type':lambda x:mp.cosh(2*x)-3*x**2}
for name,V in cases.items():
    Hs=[mp.mpf(k)/4 for k in range(1,25)]
    Rs=[R(V,H) for H in Hs]
    d=[Rs[i+1]-Rs[i] for i in range(len(Rs)-1)]
    print(name,'maxdiff',mp.nstr(max(d),5),'R(0.25)',mp.nstr(Rs[0],8),'R(6)',mp.nstr(Rs[-1],8))
V=cases['quartic a=-3,b=1']
print('pair check',mp.nstr(R(V,mp.mpf(1)),15),mp.nstr(Rpair(V,mp.mpf(1)),15))
