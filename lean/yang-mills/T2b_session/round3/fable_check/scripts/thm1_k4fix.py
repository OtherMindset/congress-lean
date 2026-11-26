# re-run of the two K4 cases where the generic grid was too coarse (quadrature error, E G0 != 1)
import numpy as np, itertools
from numpy.polynomial.legendre import leggauss
def brute(a,b,J,N,n,R):
    d=N-1; x,w=leggauss(n); x=R*x; w=R*w
    G=np.meshgrid(*([x]*N),indexing='ij'); W=np.meshgrid(*([w]*N),indexing='ij')
    S=sum(a*g**2+b*g**4 for g in G)-J*sum(G[i]*G[j] for i,j in itertools.combinations(range(N),2))
    wt=np.prod(W,axis=0)*np.exp(-(S-S.min())); wt/=wt.sum()
    E=lambda f:(wt*f).sum(); cov=lambda f,g:E(f*g)-E(f)*E(g)
    M=sum(G); Y=M/N; P2=sum(g**2 for g in G); P3=sum(g**3 for g in G); c=2*a-J*d
    G0=Y*(c*M+4*b*P3); m2=E(Y**2); m4=E(Y**4); chi=N*m2; p2=E(G[0]**2); mH2=c+12*b*p2
    D=cov(Y**2,P2); B=m4/m2**2-3
    print("a=%g b=%g n=%d R=%g EG0=%.7f VG0=%.6f formula=%.6f CSratio=%.5f 12b(-dam2)=%.6f rhs=%.6f"%(a,b,n,R,E(G0),cov(G0,G0),1+chi*mH2+12*b*D,cov(Y**2,Y**2)*cov(G0,G0)/(4*m2**2),12*b*D,2*abs(B)/(2-abs(B))-(chi*mH2-1)))
brute(3.0,0.01,1.0,4,64,5.0)
brute(-1.0,0.2,1.0,4,64,4.5)
