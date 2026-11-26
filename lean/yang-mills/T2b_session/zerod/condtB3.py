import numpy as np, time
g=np.linspace(-4.5,4.5,71); X,Y,Z=np.meshgrid(g,g,g,indexing='ij')
rng=np.random.default_rng(0); worst=np.inf; t0=time.time()
while time.time()-t0<95:
    a=rng.uniform(-1,6,3); b=rng.choice([0.1,0.5,1]); J=rng.exponential(1)*rng.choice([0.3,1]); h=rng.choice([0.02,0.1,0.4,1.0])
    lw=-a[0]*X**2-a[1]*Y**2-a[2]*Z**2-b*(X**4+Y**4+Z**4)+J*(X*Y+Y*Z+Z*X)+h*(X+Y+Z)
    w=np.exp(lw-lw.max()); w/=w.sum(); E=lambda f:(w*f).sum(); Q=X+Y+Z; Qc=Q-E(Q); m=E(X)
    for F in (X**3,X*Y**2,X*Z**2):
        N=E(F); v=(E((F-N)*Qc)*m-N*E((X-m)*Qc))/(m*N)
        if v<worst: worst=v; arg=(np.round(a,2),b,round(J,2),h)
print('3-site (B) min rel derivative',worst,arg)
