from mpmath import mp, mpf, exp, matrix
import itertools
mp.dps=40
J={(0,1):mpf('3.91908259'),(1,2):mpf('0.13505255')}
def P4(h):
    Z=0;acc={}
    S=list(itertools.product([1,-1],repeat=3))
    w=lambda s: exp(sum(J[e]*s[e[0]]*s[e[1]] for e in J)+sum(h[i]*s[i] for i in range(3)))
    Z=sum(w(s) for s in S)
    m=lambda f: sum(w(s)*f(s) for s in S)/Z
    t3=m(lambda s:s[0]*s[1]*s[2])
    return (m(lambda s:s[0])*m(lambda s:s[1]*s[2])+m(lambda s:s[1])*m(lambda s:s[0]*s[2])+m(lambda s:s[2])*m(lambda s:s[0]*s[1]))/t3
for g in ['0.001','0.01','0.05','0.1','0.2','0.5','1','2']:
    print(g, P4([mpf(0),mpf('0.0383'),mpf(g)]))
print("ray c=(0,.0383,.0218)*H")
for H in ['0.01','0.1','1','3']:
    print(H,P4([0,mpf('0.0383')*mpf(H),mpf('0.0218')*mpf(H)]))
