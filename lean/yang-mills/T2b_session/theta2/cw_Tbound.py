# CW: rigorous RW lower bound T >= sqrt((m-h chi)/(8 b h)) versus S/2, flip regime.
from cw_terms import run
a,b,J=1.0,0.5,4.0
for N in [64,256,1024,4096,16384]:
    m0=run(a,b,J,N,0.05)[0]
    for x in [0.3,1.0]:
        h=x/(N*m0); m,chi,u3,U3,U4,S=run(a,b,J,N,h)
        Tlb=((m-h*chi)/(8*b*h))**0.5
        print(f"N={N:6d} x={x} S/2={S/2:.3f}  T_lower={Tlb:8.3f}  ratio={Tlb/(S/2):7.2f}  ratio/sqrt(N)={Tlb/(S/2)/N**0.5:.3f}")
