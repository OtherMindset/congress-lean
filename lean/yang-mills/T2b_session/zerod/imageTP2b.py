import mpmath as mp
mp.mp.dps=40
def cross(ls,u,q,du,dq):
    D=lambda u,q: mp.e**ls(u-q)-mp.e**ls(u+q)
    return mp.log(D(u,q))+mp.log(D(u+du,q+dq))-mp.log(D(u,q+dq))-mp.log(D(u+du,q))
x4=lambda z:-z**4
best=None
for u in [0.1,0.3,0.6,1.0,1.5,2.0]:
    for q in [0.1,0.3,0.6,1.0,1.5,2.0]:
        c=cross(x4,mp.mpf(u),mp.mpf(q),mp.mpf('0.05'),mp.mpf('0.05'))
        if best is None or c<best[0]: best=(c,u,q)
print('x4 worst',mp.nstr(best[0],6),best[1:])
