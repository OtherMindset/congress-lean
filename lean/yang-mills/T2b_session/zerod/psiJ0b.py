import numpy as np
for (nt,nq) in [(1401,2801),(2801,5601)]:
    t=np.linspace(-7,7,nt); qg=np.linspace(-7,7,nq)
    a=-4; V=lambda x:a*x**2+x**4
    W=V((qg[:,None]+t)/np.sqrt(2))+V((qg[:,None]-t)/np.sqrt(2)); lw=-W; mx=lw.max(1,keepdims=True); w=np.exp(lw-mx)
    lr=np.log(w.sum(1))+mx[:,0]; g=(w*t**2).sum(1)/w.sum(1)
    out=[]
    for u in [0.5,1.0,1.5,2.0,2.5,3.0,3.5,4.0]:
        l=lr+np.interp(u-qg,qg,lr); ww=np.exp(l-l.max()); out.append(2*(ww*qg*g).sum()/ww.sum()/u)
    print(nt,nq,np.round(out,6))
