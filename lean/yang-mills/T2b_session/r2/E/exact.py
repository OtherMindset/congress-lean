import numpy as np, itertools, sys
def cum3(P,X,Y,Z):
    EX=(P*X).sum();EY=(P*Y).sum();EZ=(P*Z).sum()
    return (P*(X-EX)*(Y-EY)*(Z-EZ)).sum()
def run(n,a,b,J,H,ng,Lfac=1.0):
    # ring of n sites (n=2: single bond). returns dict of normalised third cumulants
    # box
    Jd = 2*J if n>2 else J
    # estimate extent: exponent <= (Jd-a)phi^2 + H|phi| - b phi^4
    c=max(Jd-a,0)
    L=0
    for L in np.arange(0.5,30,0.25):
        if b*L**4-c*L**2-H*L>45: break
    L*=Lfac
    g=np.linspace(-L,L,ng); dx=g[1]-g[0]
    shp=[1]*n
    grids=[]
    for i in range(n):
        s=[1]*n; s[i]=ng; grids.append(g.reshape(s))
    E=0
    for i in range(n):
        E=E+(H*grids[i]-a*grids[i]**2-b*grids[i]**4)
    bonds=[(0,1)] if n==2 else [(i,(i+1)%n) for i in range(n)] if n>2 else []
    for (i,j) in bonds: E=E+J*grids[i]*grids[j]
    E=E-E.max(); P=np.exp(E); P/=P.sum()
    full=np.broadcast_to
    M=sum(np.broadcast_to(gr,P.shape) for gr in grids)
    Q=[np.broadcast_to(gr**2,P.shape) for gr in grids]
    out={}
    sM=np.sqrt(((P*(M-(P*M).sum())**2).sum()))
    sq=[np.sqrt((P*(q-(P*q).sum())**2).sum()) for q in Q]
    for z in range(n):
        for w in range(z,n):
            k=cum3(P,M,Q[z],Q[w]); out[(z,w)]=k/(sM*sq[z]*sq[w])
    Qt=sum(Q); sQ=np.sqrt((P*(Qt-(P*Qt).sum())**2).sum())
    out['U']=cum3(P,M,Qt,Qt)/(sM*sQ*sQ)
    out['L']=L
    return out
if __name__=="__main__":
    print(run(2,-1,0.1,1,0.1,200))
