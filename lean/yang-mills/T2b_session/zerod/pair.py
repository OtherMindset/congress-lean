import mpmath as mp
mp.mp.dps=20
exec(open('check0d.py').read().split('import sys')[0].replace('mp.mp.dps=40',''))
V=lambda x:-3*x**2+x**4
for H in [0.3,1,2.5]:
    print(H, mp.nstr(R(V,mp.mpf(H)),12), mp.nstr(Rpair(V,mp.mpf(H)),12))
# non-GHS check: V = x^2/2 ... mixture-like potential with V' nonconvex
for name,V in {'nonGHS 6x^2-6x^4+x^6 ':lambda x:6*x**2-6*x**4+x**6, 'nonGHS 2x^2-3x^4+x^6':lambda x:2*x**2-3*x**4+x**6}.items():
    Hs=[mp.mpf(k)/8 for k in range(1,40)]; Rs=[R(V,H) for H in Hs]
    d=[(Rs[i+1]-Rs[i],Hs[i]) for i in range(len(Rs)-1)]
    print(name, mp.nstr(max(d)[0],6), max(d)[1])
