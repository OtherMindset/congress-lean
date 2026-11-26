# (V1) one-site BFS chain identity; (V4) rigorous Hartree-type bound; (V2) ring identity |B| = 12 b [ -d_a m2 + R2/N ]
from mpmath import mp, quad, exp, mpf, inf, diff
mp.dps=25
def Z(a,b,k=0): return 2*quad(lambda x: x**k*exp(-a*x*x-b*x**4),[0,1,3,8,inf])
print("V1/V4 one site:  a b | <phi^4> | 3*int dt Z(t)/Z <phi^2>_{a+4bt} | E_w[t] vs tau | 1-|B|/3 >= 1/(chi(mH2+8b chi))")
for (a,b) in [(1,0.5),(-2,1),(2,0.02),(-6,1)]:
    a=mpf(a); b=mpf(b)
    Z0=Z(a,b); p=Z(a,b,2)/Z0; x4=Z(a,b,4)/Z0
    w=lambda t: exp(-2*a*t-4*b*t*t)*Z(a+4*b*t,b)/Z0
    psi=lambda t: Z(a+4*b*t,b,2)/Z(a+4*b*t,b)
    I=quad(lambda t: w(t)*psi(t),[0,0.5,2,10,60])
    W=quad(w,[0,0.5,2,10,60]); T=quad(lambda t: t*w(t),[0,0.5,2,10,60])
    tau=x4/(3*p); B=x4/p**2-3
    mH2=2*a+12*b*p
    print(float(a),float(b),"|",mp.nstr(x4,10),mp.nstr(3*I,10),"| mass",mp.nstr(W,8),mp.nstr(p,8),"| Et",mp.nstr(T/W,8),mp.nstr(tau,8),"|",mp.nstr(1+B/3,6),">=",mp.nstr(1/(p*(mH2+8*b*p)),6))
