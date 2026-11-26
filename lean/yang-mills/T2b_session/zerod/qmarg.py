import numpy as np
t=np.linspace(-8,8,4001); q=np.linspace(0,4,801); dq=q[1]-q[0]
for a in [-3,-1,0,1,3]:
    b=1; W=a*(q[:,None]**2+t**2)+b*(q[:,None]**4+6*q[:,None]**2*t**2+t**4)/2
    lw=-W; mx=lw.max(1,keepdims=True); Vq=-(np.log(np.exp(lw-mx).sum(1))+mx[:,0])
    V2=np.gradient(np.gradient(Vq,dq),dq)
    print(a,'V_q\'\' nondecreasing on [0,4]?',np.all(np.diff(V2[5:-5])>=-1e-6), 'min diff',np.diff(V2[5:-5]).min())
