# One-site checks: (O5) third cumulant; Prop 7.2 walk bounds (1)-(3) with exact quadrature (mpmath).
import mpmath as mp
mp.mp.dps=30
def moments(a,b,H,ks=range(7)):
    f=lambda x,k: x**k*mp.exp(-a*x**2-b*x**4+H*x)
    # peak locations for splitting
    Z=[mp.quad(lambda x:f(x,k),[-mp.inf,-3,-1,0,1,3,mp.inf]) for k in ks]
    return [z/Z[0] for z in Z]
def cum3_phi_phi2_phi2(a,b,H):
    m=moments(a,b,H)
    # joint cumulant k(X,Y,Y), X=phi, Y=phi^2 : E[XYY]-E[X]E[YY]-2E[Y]E[XY]+2E[X]E[Y]^2
    EX=m[1];EY=m[2];EXY=m[3];EYY=m[4];EXYY=m[5]
    k=EXYY-EX*EYY-2*EY*EXY+2*EX*EY**2
    # also as second a-derivative of m numerically
    d=mp.mpf('1e-5')
    mm=lambda aa: moments(aa,b,H,ks=range(2))[1]
    d2=(mm(a+d)-2*mm(a)+mm(a-d))/d**2
    sd=lambda v:mp.sqrt(v)
    norm=k/(sd(m[2]-m[1]**2)*(m[4]-m[2]**2))
    return k,d2,norm
print("O5:",cum3_phi_phi2_phi2(mp.mpf('-1.896'),mp.mpf('0.336'),mp.mpf('1.493')))
print("O5 (team pt):",cum3_phi_phi2_phi2(mp.mpf('-1.89611722'),mp.mpf('0.33582423'),mp.mpf('1.49270288')))

# Walk quantities on one site. g(s)=exp(-2a s-4b s^2), Z(t)=int e^{H phi} g(phi^2/2+t) dphi
def walk(a,b,H):
    Zt=lambda t: mp.quad(lambda x: mp.exp(H*x-2*a*(x**2/2+t)-4*b*(x**2/2+t)**2),[-mp.inf,-3,-1,0,1,3,mp.inf])
    Z0=Zt(0)
    m=moments(a,b,H,ks=range(4))
    chi=m[2]-m[1]**2
    # w0(dT) = H dT Z(T)/Z  (mass m) -- check
    mass=H*mp.quad(lambda T:Zt(T),[0,1,3,mp.inf])/Z0
    Told=mp.quad(lambda T:T*Zt(T),[0,1,3,mp.inf])/Z0
    T=H*Told          # T with mass-m normalisation
    # m^{(r)}: magnetisation with a->a+4b r
    mr=lambda r: moments(a+4*b*r,b,H,ks=range(2))[1]
    rhs1=H*mp.quad(lambda t: Zt(t)/Z0*mr(t),[0,1,3,mp.inf])  # int w0 m^{(t)}
    S=m[3]-m[1]*m[2]   # -d_a m = <phi;phi^2>
    lhs=m[1]-H*chi
    Keff=lhs/(4*b*H*T*S)
    # Keff from definition: E_w0[M(a)-M(a+4bt)]/E_w0[4bt S]
    num=H*mp.quad(lambda t: Zt(t)/Z0*(m[1]-mr(t)),[0,1,3,mp.inf])
    den=H*mp.quad(lambda t: Zt(t)/Z0*4*b*t*S,[0,1,3,mp.inf])
    return dict(m=m[1],mass=mass,HT=H*T,HT_from_identity=rhs1,m2=m[1]**2,
        HTold=H*Told, m_minus_Hchi=lhs, bound2=8*b*H*T**2, ratio2=8*b*H*T**2/lhs,
        bound2_oldnorm=8*b*H*Told**2, W3=H*num, Keff_def=num/den, Keff_from3=Keff)
for p in [(2,0.02,0.5),(2,0.2,0.5),(1,1,1),(0,1,1),(-2,1,1),(-2,1,0.1),(1,0.1,0.05)]:
    r=walk(*[mp.mpf(x) for x in p]); print(p,{k:mp.nstr(v,8) for k,v in r.items()})
