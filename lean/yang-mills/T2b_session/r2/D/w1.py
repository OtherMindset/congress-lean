import mpmath as mp
mp.mp.dps=20
def M(a,b,H):
    w=lambda x: mp.exp(-a*x**2-b*x**4+H*x)
    return mp.quad(lambda x:x*w(x),[-mp.inf,0,mp.inf])/mp.quad(w,[-mp.inf,0,mp.inf])
def chk(a,b,H):
    a,b,H=map(mp.mpf,(a,b,H))
    w=lambda x: mp.exp(-a*x**2-b*x**4+H*x); Z=mp.quad(w,[-mp.inf,0,mp.inf])
    Zh=lambda t: mp.quad(lambda x:w(x)*mp.exp(-2*a*t-4*b*(x**2*t+t**2)),[-mp.inf,0,mp.inf])/Z
    m=M(a,b,H)
    HT=H*H*mp.quad(lambda t:t*Zh(t),[0,1,mp.inf])
    W1=H*mp.quad(lambda t:Zh(t)*M(a+4*b*t,b,H),[0,1,mp.inf])
    print((float(a),float(b),float(H)),"HT",mp.nstr(HT,10),"int w0 m^(t)",mp.nstr(W1,10),"m^2",mp.nstr(m*m,10))
chk(1,1,0.3); chk(-2,1,0.3)
