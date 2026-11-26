import numpy as np, mpmath as mp
mp.mp.dps=30
a=[mp.mpf('0.66365669'),mp.mpf('0.84555844'),mp.mpf('1.50632064')]; beta=mp.mpf('1.3360783867291268')
# exact density: Z(H)=e^{beta H^2} prod(1+H^2/a^2) <-> g * prod(1 + D^2/a^2) applied... H^2 <-> d^2/dx^2 acting on density (Laplace: int e^{Hx} g'' = H^2 Z_g)
s2=2*beta
g=lambda x: mp.e**(-x**2/(2*s2))/mp.sqrt(2*mp.pi*s2)
# polynomial in D: coefficients
c=[mp.mpf(1)]
for ak in a:
    new=[mp.mpf(0)]*(len(c)+2)
    for i,ci in enumerate(c): new[i]+=ci; new[i+2]+=ci/ak**2
    c=new
def f(x): return sum(ci*mp.diff(g,x,i) for i,ci in enumerate(c) if ci!=0)
xs=[mp.mpf(k)/10 for k in range(0,150)]
vals=[f(x) for x in xs]; print('min density',mp.nstr(min(vals),8),'at',xs[vals.index(min(vals))])
# polynomial form: f = g * P(x); get P by evaluating f/g at points? directly use quadrature of R(H)
def R(H):
    mom=[mp.quad(lambda x: x**n*f(x)*mp.e**(H*x),[-30,-10,0,10,30]) for n in range(4)]
    m1,m2,m3=[mom[i]/mom[0] for i in (1,2,3)]
    return (m3-m1*m2)/m1, mom[0]
for H in [2.0,2.5,3.0,3.5,4.0]:
    r,Z=R(mp.mpf(H)); Zth=mp.e**(beta*H**2)*mp.fprod([1+H**2/ak**2 for ak in a])
    print(H,mp.nstr(r,15),'Z check',mp.nstr(Z/Zth,10))
