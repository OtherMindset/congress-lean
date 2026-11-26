/* Lattice phi^4 on an L x L periodic torus.
   Weight: exp( sum_<xy> phi_x phi_y + H sum_x phi_x - sum_x (a phi_x^2 + b phi_x^4) ),
   each nearest-neighbour bond of the torus counted once (2N bonds; for L=2 this is the
   multigraph in which each neighbouring pair is joined by 2 bonds).
   Updates per "sweep": 1 Metropolis sweep, 1 overrelaxation sweep (reflection about the
   Gaussian part, accepted with the quartic factor), Wolff embedded-cluster moves
   (Brower-Tamayo) until >= N sites have been visited; the cluster flip is accepted with
   min(1, exp(-2 H sum_cluster phi)).
   Output (binary, doubles): per measurement A = N^-1 sum phi, B = N^-1 sum phi^2,
   C = N^-1 sum phi^3, F = |phi~(k_min)|^2/N (avg of two axes).
   usage: phi4 L a b H ntherm nmeas every seed outfile [phi_init]
*/
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>

static uint64_t s[4];
static inline uint64_t rotl(const uint64_t x, int k){ return (x << k) | (x >> (64 - k)); }
static inline uint64_t nextr(void){
  const uint64_t r = rotl(s[1] * 5, 7) * 9; const uint64_t t = s[1] << 17;
  s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
  return r; }
static inline double U(void){ return (nextr() >> 11) * 0x1.0p-53; }
static void seedrng(uint64_t x){ for(int i=0;i<4;i++){ x += 0x9e3779b97f4a7c15ULL;
  uint64_t z = x; z = (z ^ (z>>30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z>>27)) * 0x94d049bb133111ebULL;
  s[i] = z ^ (z>>31);} }

int MODE=7; int NCL=1; int L, N; double a, b, H; double *phi; int *nb; int *stack; char *inc;

static double metro(double step){
  int acc = 0;
  for(int x=0;x<N;x++){
    double J = phi[nb[4*x]]+phi[nb[4*x+1]]+phi[nb[4*x+2]]+phi[nb[4*x+3]] + H;
    double p = phi[x], q = p + step*(2*U()-1);
    double p2=p*p, q2=q*q;
    double dS = a*(q2-p2) + b*(q2*q2-p2*p2) - J*(q-p);
    if(dS <= 0 || U() < exp(-dS)){ phi[x]=q; acc++; }
  }
  return (double)acc/N;
}
static double overrelax(void){
  int acc=0;
  for(int x=0;x<N;x++){
    double J = phi[nb[4*x]]+phi[nb[4*x+1]]+phi[nb[4*x+2]]+phi[nb[4*x+3]] + H;
    double p = phi[x], q = J/a - p;   /* a phi^2 - J phi invariant (a>0 assumed) */
    double p2=p*p, q2=q*q;
    double dS = b*(q2*q2-p2*p2);
    if(dS <= 0 || U() < exp(-dS)){ phi[x]=q; acc++; }
  }
  return (double)acc/N;
}
static int wolff(void){
  int x0 = (int)(U()*N); int sp=0, size=0; double sum=0;
  int sg = phi[x0] > 0; stack[sp++] = x0; inc[x0]=1;
  /* stack doubles as cluster list: keep all members in list[0..size) */
  int head = 0;
  while(head < sp){
    int x = stack[head++]; size++; sum += phi[x];
    for(int k=0;k<4;k++){ int y = nb[4*x+k];
      if(!inc[y] && ((phi[y]>0)==sg)){
        double pr = 1.0 - exp(-2.0*phi[x]*phi[y]);
        if(U() < pr){ inc[y]=1; stack[sp++]=y; } } }
  }
  int flip = 1;
  if(H != 0){ double dS = 2.0*H*sum; if(dS > 0 && U() >= exp(-dS)) flip = 0; }
  for(int i=0;i<sp;i++){ int x=stack[i]; inc[x]=0; if(flip) phi[x] = -phi[x]; }
  return size;
}
static void sweep(double step){
  if(MODE&1) metro(step); if(MODE&2) overrelax();
  if(MODE&4){ for(int c=0;c<NCL;c++) wolff(); }
}
int main(int argc, char **argv){
  if(argc < 9){ fprintf(stderr,"usage\n"); return 1; }
  L=atoi(argv[1]); a=atof(argv[2]); b=atof(argv[3]); H=atof(argv[4]);
  long nth=atol(argv[5]), nmeas=atol(argv[6]); int every=atoi(argv[7]);
  seedrng((uint64_t)atoll(argv[8])); FILE *f = fopen(argv[9],"wb");
  double init = argc>10 ? atof(argv[10]) : 0.0; if(getenv("MODE")) MODE=atoi(getenv("MODE"));
  N=L*L; phi=malloc(N*sizeof(double)); nb=malloc(4*N*sizeof(int)); stack=malloc(N*sizeof(int)); inc=calloc(N,1);
  for(int i=0;i<L;i++) for(int j=0;j<L;j++){ int x=i*L+j;
    nb[4*x]=((i+1)%L)*L+j; nb[4*x+1]=((i-1+L)%L)*L+j; nb[4*x+2]=i*L+(j+1)%L; nb[4*x+3]=i*L+(j-1+L)%L; }
  for(int x=0;x<N;x++) phi[x] = init + 0.1*(2*U()-1);
  double step = 1.0;
  long csum=0, ccnt=0;
  for(long t=0;t<nth;t++){ double ac = metro(step); overrelax(); int tot=0; while(tot<N){ tot+=wolff(); ccnt++; } csum+=tot;
    if(ac > 0.55) step *= 1.05; else if(ac < 0.45) step /= 1.05; }
  /* fixed number of clusters per sweep (state-independent), so the chain is stationary */
  { double mean = (double)csum/(ccnt>0?ccnt:1); NCL = (int)ceil(N/mean); if(NCL<1) NCL=1; if(NCL>N) NCL=N; }
  fprintf(stderr,"NCL=%d ",NCL);
  double buf[4]; double *ck=malloc(L*sizeof(double)), *sk=malloc(L*sizeof(double));
  for(int i=0;i<L;i++){ ck[i]=cos(2*M_PI*i/L); sk[i]=sin(2*M_PI*i/L); }
  double *row=calloc(L,sizeof(double)), *col=calloc(L,sizeof(double));
  for(long t=0;t<nmeas;t++){
    for(int k=0;k<every;k++) sweep(step);
    double A=0,B=0,C=0; for(int i=0;i<L;i++){row[i]=0;col[i]=0;}
    for(int i=0;i<L;i++) for(int j=0;j<L;j++){ double p=phi[i*L+j], p2=p*p; A+=p; B+=p2; C+=p2*p; row[i]+=p; col[j]+=p; }
    double c1=0,s1=0,c2=0,s2=0; for(int i=0;i<L;i++){ c1+=ck[i]*row[i]; s1+=sk[i]*row[i]; c2+=ck[i]*col[i]; s2+=sk[i]*col[i]; }
    buf[0]=A/N; buf[1]=B/N; buf[2]=C/N; buf[3]=0.5*(c1*c1+s1*s1+c2*c2+s2*s2)/N; fwrite(buf,sizeof(double),4,f);
  }
  fclose(f); fprintf(stderr,"done step=%g\n",step); return 0;
}
