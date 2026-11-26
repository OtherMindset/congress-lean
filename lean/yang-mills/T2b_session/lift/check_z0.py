import numpy as np, sys
sys.path.insert(0,'.')
from pointwise_test import two_site
for (a,b,J,h0,h1) in [(-2.541,0.023,0.473,0.0,0.012),(-1.612,0.083,0.854,0.0,0.065),(-1.853,0.549,4.428,0.021,0.153)]:
    for n,L in [(1201,None),(2401,None),(2401,14.0),(3201,20.0)]:
        r=two_site(a,b,J,h0,h1,n=n,L=L)
        print(a,b,J,h0,h1,n,L,[ (v, v/s) for v,s in r])
