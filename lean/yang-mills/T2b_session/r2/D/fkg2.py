import numpy as np
rng=np.random.default_rng(1)
x=np.linspace(-6,6,801); X,Y=np.meshgrid(x,x,indexing='ij')
worst=1e9
for trial in range(300):
    a=rng.uniform(-3,2.5); b=rng.uniform(0.05,1.5); J=rng.uniform(0,2); H=rng.uniform(0,2)
    base=-a*(X**2+Y**2)-b*(X**4+Y**4)+J*X*Y+H*(X+Y); base-=base.max(); P=np.exp(base); P/=P.sum()
    sX,sY=X**2/2,Y**2/2
    def E(t): return np.exp(-2*a*t[0]-4*b*(2*sX*t[0]+t[0]**2))*np.exp(-2*a*t[1]-4*b*(2*sY*t[1]+t[1]**2))
    t1=rng.exponential(0.5,2); t2=rng.exponential(0.5,2)
    lhs=(P*E(t1+t2)).sum(); rhs=np.exp(-8*b*(t1@t2))*(P*E(t1)).sum()*(P*E(t2)).sum()
    worst=min(worst,lhs/rhs-1)
print("min over 300 random (a,b,J,H,t1,t2) of Zhat(t1+t2)/(e^{-8b t1.t2} Zhat(t1)Zhat(t2)) - 1 =",worst)
