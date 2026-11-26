# Is D(u,q)=s(u-q)-s(u+q) TP2 on (0,inf)^2 for even log-concave s?  check min over grid of log-mixed-derivative
import numpy as np
x=np.linspace(0.02,6,300)
U,Q=np.meshgrid(x,x,indexing='ij')
tests={'gauss':lambda z:-z**2/2,'laplace':lambda z:-np.abs(z),'x4':lambda z:-z**4,'x4+x2':lambda z:-z**4-0.3*z**2,
 'logcosh':lambda z:-np.log(np.cosh(3*z)),'huber':lambda z:-np.where(np.abs(z)<1,z**2/2,np.abs(z)-0.5),'x8':lambda z:-z**8,
 'uniform-ish':lambda z:-(np.abs(z)/1.5)**30}
for n,ls in tests.items():
    D=np.exp(ls(U-Q))-np.exp(ls(U+Q))
    L=np.log(np.maximum(D,1e-300))
    # discrete TP2: L(i,j)+L(i+1,j+1)-L(i,j+1)-L(i+1,j) >=0
    m=L[:-1,:-1]+L[1:,1:]-L[:-1,1:]-L[1:,:-1]
    ok=D>1e-200; okm=ok[:-1,:-1]&ok[1:,1:]&ok[:-1,1:]&ok[1:,:-1]
    print(n,'min TP2 cross diff',m[okm].min())
