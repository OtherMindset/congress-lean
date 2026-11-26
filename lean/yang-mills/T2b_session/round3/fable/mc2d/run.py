import subprocess, os, sys, numpy as np, json
b=float(sys.argv[1]); L=int(sys.argv[2]); n=int(sys.argv[3])
ac={0.5:0.905,0.1:1.71,0.02:1.927}[b]; sc={0.5:1.0,0.1:0.5,0.02:0.2}[b]
ds=[-0.3,-0.2,-0.15,-0.1,-0.07,-0.05,-0.03,-0.02,-0.01,0,0.01,0.02,0.03,0.05,0.07,0.1,0.15,0.2,0.3,0.4,0.6,0.8,1.0,1.3,1.6,2.0]
out={}
for i,d in enumerate(ds):
    a=round(ac+d*sc,5); fn=f'r_b{b}_L{L}_{i}.bin'
    subprocess.run(['/home/claude/t2b/mc/phi4',str(L),str(a),str(b),'0.0','4000',str(n),'1',str(100+i+1000*L),fn,'0.5'],check=True,stdout=subprocess.DEVNULL)
    A=np.fromfile(fn).reshape(-1,4)[:,0]; os.remove(fn)
    nb=50; bl=A[:len(A)//nb*nb].reshape(nb,-1)
    out[a]=dict(m2b=(bl**2).mean(1).tolist(), m4b=(bl**4).mean(1).tolist())
    json.dump(out,open(f'res_b{b}_L{L}.json','w'))
