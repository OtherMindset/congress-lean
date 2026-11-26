import numpy as np
t=np.linspace(-8,8,3201); zg=np.linspace(-14,14,5601)
x=np.linspace(0.02,6,240); U,Q=np.meshgrid(x,x,indexing='ij')
for a,b in [(2,0.01),(2,0.1),(2,1),(0.5,1),(0.1,1),(1,1)]:
    V=lambda y:a*y**2+b*y**4
    W=V((zg[:,None]+t)/np.sqrt(2))+V((zg[:,None]-t)/np.sqrt(2)); lw=-W; mx=lw.max(1,keepdims=True)
    lr=np.log(np.exp(lw-mx).sum(1))+mx[:,0]
    for N in [2,3]:
        if N==2: ls=lr
        else:
            r=np.exp(lr-lr.max()); c=np.convolve(r,r,'same'); ls=np.log(np.maximum(c,1e-300))
        f=lambda z: np.interp(z,zg,ls)
        # D/s(u) scaled to avoid underflow: D = s(u-q)-s(u+q)
        A=f(U-Q); B=f(U+Q); L=A+np.log1p(-np.exp(np.minimum(B-A,-1e-16)))
        m=L[:-1,:-1]+L[1:,1:]-L[:-1,1:]-L[1:,:-1]
        print('a',a,'b',b,'N',N,'min TP2 cross',m.min())
