from b3 import *
n=2;ed=[(0,1)];J=[0.5];c=np.array([1.0,0.7]);H=0.4
S,w=spin_data(n,ed,J,c,H)
for (k,i,j) in [(0,0,1),(1,0,1)]:
    num,ZA,Z0=trunc_check(n,ed,J,H*c,12,k,i,j)
    A=set([k,n])^set([i,j])
    print(A,"ZA/Z0",ZA/Z0, "spin", ev(w,S[:,list(A-{n})].prod(1)) if n not in A else ev(w,S[:,list(A-{n})].prod(1)))
    print(cov(w,S[:,k]*1.,S[:,i]*S[:,j]*1.), num/Z0)
