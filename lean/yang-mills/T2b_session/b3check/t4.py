from t3 import *
import math
# item 2: series check of conditional parity laws
for w in (0.1,0.7,2.3):
    a=np.arange(0,100); pm=w**a/np.array([math.factorial(int(x)) for x in a],float)
    od=a%2==1
    print(w,"odd",(a*pm)[od].sum()/pm[od].sum()-w/np.tanh(w),"even",(a*pm)[~od].sum()/pm[~od].sum()-w*np.tanh(w), "f",w/np.tanh(w)-w*np.tanh(w)-2*w/np.sinh(2*w))
# discrimination: non-constant c on B (IC false there) and base-field-like; compare signs
import sys
n=4;bad=0;viol=0;tot=0;nv_naive_detect=0;mism=0
for t in range(int(sys.argv[1])):
    edges,J,c,H,B=instance(n)
    c=rng.uniform(0,2,n)      # nonconstant on B
    S_,dlogS,S,w=spin_IC(n,edges,J,c,H,B)
    # for nonconstant c the currents argument still holds with w=Hc; K identity unaffected
    bc=bulk_configs(n,edges,J); o=measures(n,edges,J,H*c,B,bc)
    Nn,D,Nt=o['Nnaive'],o['D'],o['Ntrue']
    d12=Nn[2]/Nn[0]-D[2]/D[0]; dcor=(Nt[1]/Nt[0]-D[1]/D[0])
    tot+=1
    if dlogS>0: viol+=1
    if np.sign(d12)!=np.sign(dlogS): mism+=1
    assert abs(H*dlogS-dcor)<1e-9
print("nonconst c: trials",tot,"IC violations",viol,"naive sign mismatches",mism)
