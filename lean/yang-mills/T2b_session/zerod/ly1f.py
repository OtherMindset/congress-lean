import numpy as np
exec(open('ly1.py').read().split('def positive')[0])
Hs=np.geomspace(1e-3,100,3000)
print('one factor a=1:')
for beta in [0.5,0.51,0.6,0.75,1,2,5]:
    T=np.array([T_of(np.array([1.]),beta,H)[0] for H in Hs]); print(beta, 'max T',T.max(),'at H',Hs[T.argmax()])
print('k equal zeros a=1, beta=k/2 (boundary of sufficient positivity):')
for k in [2,3,4,6]:
    for beta in [k/2, k/2*1.2]:
        T=np.array([T_of(np.ones(k),beta,H)[0] for H in Hs]); print(k,beta,'max T',T.max(),'at H',Hs[T.argmax()])
