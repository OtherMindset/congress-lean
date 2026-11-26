import numpy as np
x=np.linspace(-8,8,8001); dx=x[1]-x[0]
def R(V,H):
    lw=-V(x)+H*x; w=np.exp(lw-lw.max()); Z=w.sum()
    m1,m2,m3=[(w*x**k).sum()/Z for k in (1,2,3)]; return (m3-m1*m2)/m1
def Rpair(V,H):
    q=np.linspace(0,6,1201)[1:,None]; t=np.linspace(-8,8,1601)[None,:]
    W=V((q+t)/np.sqrt(2))+V((q-t)/np.sqrt(2)); lw=-W; mx=lw.max(1,keepdims=True); w=np.exp(lw-mx)
    rho=w.sum(1); lrho=np.log(rho)+mx[:,0]; g=(w*t**2).sum(1)/rho; qq=q[:,0]; h=np.sqrt(2)*H
    lp=np.log(qq)+h*qq+np.log1p(-np.exp(-2*h*qq))+lrho; p=np.exp(lp-lp.max())
    return 2*(p*g).sum()/p.sum(), np.all(np.diff(g)<=1e-12)
V=lambda x:-3*x**2+x**4
for H in [0.3,1,2.5]: print('pair',H,R(V,H),Rpair(V,H))
cases={'6x2-6x4+x6 (nonGHS)':lambda x:6*x**2-6*x**4+x**6,'2x2-3x4+x6 (nonGHS)':lambda x:2*x**2-3*x**4+x**6,
'x2+x4':lambda x:x**2+x**4,'-20x2+x4':lambda x:-20*x**2+x**4,'cosh(2x)-3x2':lambda x:np.cosh(2*x)-3*x**2,'x^2/2+|x|^3':lambda x:x**2/2+abs(x)**3,
'-x2 + x8':lambda x:-x**2+x**8}
for n,V in cases.items():
    Hs=np.linspace(0.01,6,600); Rs=np.array([R(V,H) for H in Hs]); d=np.diff(Rs)
    print(n,'max dR',d.max(),'at H',Hs[d.argmax()], 'g monotone', Rpair(V,1.0)[1])
