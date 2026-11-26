import numpy as np, itertools, mpmath as mp
mp.mp.dps=50
def Sderiv(J,B,H):
    n=len(J); tot=[mp.mpf(0)]*1
    acc={}
    keys=['1','a','a2','a3','M','aM','a2M','a3M']
    s={k:mp.mpf(0) for k in keys}
    for sp in itertools.product([-1,1],repeat=n):
        E=sum(J[i][j]*sp[i]*sp[j] for i in range(n) for j in range(i+1,n) if J[i][j]!=0)
        M=sum(sp); a=sum(sp[i] for i in B)
        w=mp.e**(mp.mpf(E)+H*M)
        s['1']+=w; s['a']+=w*a; s['a2']+=w*a*a; s['a3']+=w*a**3; s['M']+=w*M; s['aM']+=w*a*M; s['a2M']+=w*a*a*M; s['a3M']+=w*a**3*M
    E={k:v/s['1'] for k,v in s.items()}
    m=E['a']; c=E['a3']-E['a']*E['a2']   # <a;a^2>
    # d/dH of c = <a^3;M> - <a;M><a2> - <a><a2;M>
    dc=(E['a3M']-E['a3']*E['M'])-(E['aM']-E['a']*E['M'])*E['a2']-E['a']*(E['a2M']-E['a2']*E['M'])
    dm=E['aM']-E['a']*E['M']
    return (dc*m-c*dm)/m**2, c/m
