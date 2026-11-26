import mpmath as mp
mp.mp.dps=30
def run(a,b,H):
    a,b,H=mp.mpf(a),mp.mpf(b),mp.mpf(H)
    w=lambda x: mp.exp(-a*x**2-b*x**4+H*x)
    I=lambda f: mp.quad(lambda x:f(x)*w(x),[-mp.inf,-2,0,2,mp.inf])
    Z=I(lambda x:1); m=I(lambda x:x)/Z; m2=I(lambda x:x**2)/Z; chi=m2-m**2
    # int_0^inf t^k g(s+t) dt with g(u)=exp(-2a u-4b u^2), s=x^2/2
    def G(x,k):
        s=x**2/2
        return mp.quad(lambda t: t**k*mp.exp(-2*a*t-4*b*(2*s*t+t**2)),[0,1,mp.inf])
    # Zhat(t)=<g(s+t)/g(s)>; int Zhat t^k dt = <int t^k g(s+t)/g(s) dt>
    m_w=H*I(lambda x:G(x,0))/Z; T=H*I(lambda x:G(x,1))/Z
    S=2*(I(lambda x:x**3)/Z-m*m2)  # one site: S = d_H<phi^2> = <phi;phi^2>... check
    return m,m_w,m-H*chi,8*b*H*T**2,T,(I(lambda x:x**3)/Z-m*m2)/2
for p in [(2,0.02,0.5),(2,0.02,0.1),(2,0.02,2),(2,0.2,0.5),(1,1,0.3)]:
    m,mw,l,r,T,Shalf=run(*p)
    print(p, "m",mp.nstr(m,10),"m_walk",mp.nstr(mw,10)," m-Hchi",mp.nstr(l,8)," 8bHT^2",mp.nstr(r,8)," ratio",mp.nstr(r/l,6)," T",mp.nstr(T,8)," S/2",mp.nstr(Shalf,8))
