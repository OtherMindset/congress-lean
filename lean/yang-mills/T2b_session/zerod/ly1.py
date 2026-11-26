import numpy as np
rng=np.random.default_rng(0)
def T_of(a,beta,H):
    w=a**2+H**2; v=1/w; y=H**2*v
    k1=H*(2*beta+2*v.sum()); k2=2*beta+(v*(2-4*y)).sum()
    k3=H*(v**2*(-12+16*y)).sum(); k4=(v**2*(-12+96*y-96*y**2)).sum()
    return 2*k1**2*k3+k1*k4-k2*k3, k1
def positive(a,beta):
    # density of e^{beta H^2} prod(1+H^2/a^2): g * prod(1 + D^2/a^2) applied; check numerically via polynomial coefficients
    if beta<=0: return False
    x=np.linspace(-40*np.sqrt(beta)-5,40*np.sqrt(beta)+5,4001)
    # use Hermite-like: apply operator to gaussian numerically with spectral method
    from numpy.polynomial import hermite_e as He
    # gaussian with variance 2beta; derivative operator: D^{2n} g = g * He_{2n}(x/s)/s^{2n} with s=sqrt(2beta)
    s=np.sqrt(2*beta); poly=np.array([1.])
    from numpy.polynomial import polynomial as P
    for ak in a: poly=P.polymul(poly,[1,0,1/ak**2])  # in D
    dens=np.zeros_like(x)
    for n,c in enumerate(poly):
        if c==0: continue
        e=np.zeros(n+1); e[n]=1; dens+=c*He.hermeval(x/s,e)*(-1/s)**n
    return dens.min()>-1e-12*np.abs(dens).max()
worstpos=-np.inf; worstall=-np.inf
for t in range(40000):
    n=rng.integers(1,6); a=rng.exponential(1,n)*rng.choice([0.3,1,3],n); beta=rng.choice([0,rng.exponential(1)])
    pos=positive(a,beta) if t%4==0 else None
    for H in np.geomspace(1e-2,30,25):
        T,k1=T_of(a,beta,H)
        scale=k1**2*abs(k1)/H**2+1e-300
        r=T/abs(scale)
        if r>worstall: worstall=r; wa=(a,beta,H)
        if pos and r>worstpos: worstpos=r; wp=(a,beta,H)
print('all',worstall,wa); print('positive',worstpos, wp if worstpos>-np.inf else None)
