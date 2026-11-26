import mpmath as mp, numpy as np
mp.mp.dps=30
exec(open('ly1.py').read().split('worstpos=')[0])
a=np.array([0.31177906, 0.03222347, 0.94691914, 0.07232476, 0.25784694]); beta=0.005641879242057459; H=5.658756330071741
L=lambda h: beta*h**2+sum(mp.log(1+h**2/ak**2) for ak in a)
k=[mp.diff(L,H,n) for n in range(1,5)]
print('direct T',2*k[0]**2*k[2]+k[0]*k[3]-k[1]*k[2],' formula',T_of(a,beta,H))
print('positive?',positive(a,beta))
# direct density check: Z(H) for positive measure must be log-convex: k2>0 for all H
print('k2 at H',k[1])
