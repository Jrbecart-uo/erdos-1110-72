// Independent verifier for the two-block-lookahead potential certificate, (p,q)=(7,2).
// Chains: sets {(alpha,gamma)} strictly increasing in both, alpha<s, gamma<H, value v = sum 2^alpha 7^{-gamma} mod 2^{3s}.
// Uses ANY subset of chains per residue (here: min height + SLACK), so min over fewer chains is conservative.
// State x=(c,b1); fresh u; z = c + 2^s b1 + 2^{2s} u (mod 2^{3s}); for chain C with v = c mod 2^s:
//   w = ((z - v) mod 2^{3s}) >> s ;  zn = 7^h * w mod 2^{2s} ; next = (zn mod 2^s, zn >> s).
// Checks  sum_u min_C [h*SC + Vi(next)] - S*Vi(x) <= GNUM  for all x, reports GNUM (exact int64),
// then ghat = GNUM/(S*SC) and compares with a rational lower bound a/b <= log_7 2 (7^a <= 2^b checked separately).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64; typedef int64_t i64;
int s,H,SLACK; u64 S,MS,M3;
typedef struct{ u64 v; int h; } Ch; Ch *ch; u64 nch=0,cap=0; u64 *u7;
void add(u64 v,int h){ if(nch==cap){cap=cap?cap*2:1<<20; ch=realloc(ch,cap*sizeof(Ch));} ch[nch].v=v; ch[nch].h=h; nch++; }
void gen(int a0,int g0,u64 v,int h){ add(v,h);
  for(int a=a0;a<s;a++) for(int g=g0;g<H;g++) gen(a+1,g+1,(v+((u7[g]<<a)&(M3-1)))&(M3-1),g+1); }
int cmpc(const void*a,const void*b){ u64 x=((Ch*)a)->v&MS, y=((Ch*)b)->v&MS; return x<y?-1:x>y; }
int main(int argc,char**argv){
  s=atoi(argv[1]); H=atoi(argv[2]); SLACK=atoi(argv[3]); const char*vf=argv[4]; int SCB=20; i64 SC=1LL<<SCB;
  S=1ULL<<s; MS=S-1; M3=1ULL<<(3*s);
  // 7^{-1} mod 2^64 by Newton, then powers mod 2^{3s}
  u64 inv=1; for(int i=0;i<7;i++) inv*=2-7*inv; if((inv*7)!=1){fprintf(stderr,"inv fail\n");return 1;}
  u7=malloc(8*(H+1)); u7[0]=1; for(int g=1;g<=H;g++) u7[g]=(u7[g-1]*inv)&(M3-1);
  gen(0,0,0,0); qsort(ch,nch,sizeof(Ch),cmpc);
  u64 *st=calloc(S+1,8); for(u64 i=0;i<nch;i++) st[(ch[i].v&MS)+1]++; for(u64 c=0;c<S;c++) st[c+1]+=st[c];
  // prune: per residue keep h <= minh + SLACK
  Ch *pk=malloc(nch*sizeof(Ch)); u64 *ps=calloc(S+1,8); u64 w=0;
  for(u64 c=0;c<S;c++){ if(st[c+1]==st[c]){fprintf(stderr,"residue %llu uncovered\n",(unsigned long long)c);return 1;}
    int mh=99; for(u64 j=st[c];j<st[c+1];j++) if(ch[j].h<mh) mh=ch[j].h;
    ps[c]=w; for(u64 j=st[c];j<st[c+1];j++) if(ch[j].h<=mh+SLACK) pk[w++]=ch[j]; }
  ps[S]=w;
  // sanity: each kept chain value really ≡ c mod 2^s (by construction of bucketing) — recheck
  for(u64 c=0;c<S;c++) for(u64 j=ps[c];j<ps[c+1];j++) if((pk[j].v&MS)!=c){fprintf(stderr,"bucket error\n");return 1;}
  float *V=malloc(4*S*S); FILE*f=fopen(vf,"rb"); if(!f||fread(V,4,S*S,f)!=S*S){fprintf(stderr,"read V fail\n");return 1;} fclose(f);
  i64 *Vi=malloc(8*S*S);
  for(u64 x=0;x<S*S;x++){ if(!isfinite(V[x]) || fabs(V[x])>1e6){fprintf(stderr,"bad V entry %llu\n",(unsigned long long)x);return 1;}
    Vi[x]=(i64)llround((double)V[x]*SC); }
  u64 p7[64]; p7[0]=1; for(int i=1;i<=H;i++) p7[i]=p7[i-1]*7;
  i64 G=INT64_MIN; u64 Gx=0;
  // optional: per-state values for states listed in argv[7] (one index per line)
  u64 *probe=NULL; int np=0; if(argc>7){ FILE*pf=fopen(argv[7],"r"); probe=malloc(8*100000); unsigned long long q; while(np<100000 && fscanf(pf,"%llu",&q)==1) probe[np++]=q; fclose(pf); }
  #pragma omp parallel
  { i64 lg=INT64_MIN; u64 lx=0;
    #pragma omp for schedule(dynamic,64)
    for(u64 x=0;x<S*S;x++){
      u64 c=x>>s, b1=x&MS; i64 tot=0;
      for(u64 uu=0;uu<S;uu++){
        u64 z=(c | (b1<<s) | (uu<<(2*s)));
        i64 best=INT64_MAX;
        for(u64 j=ps[c];j<ps[c+1];j++){
          u64 wv=((z - pk[j].v)&(M3-1))>>s;
          u64 zn=(p7[pk[j].h]*wv)&((1ULL<<(2*s))-1);
          u64 idx=((zn&MS)<<s) | (zn>>s);
          i64 v2=(i64)pk[j].h*SC + Vi[idx];
          if(v2<best) best=v2;
        }
        tot+=best;
      }
      i64 d=tot-(i64)S*Vi[x]; if(d>lg){ lg=d; lx=x; }
      for(int q=0;q<np;q++) if(probe[q]==x){
        #pragma omp critical
        printf("probe state %llu d=%lld\n",(unsigned long long)x,(long long)d);
      }
    }
    #pragma omp critical
    { if(lg>G){ G=lg; Gx=lx; } }
  }
  // rational lower bound for log_7 2: a/b with 7^a <= 2^b  (checked in python separately)
  long a=atol(argv[5]), b=atol(argv[6]);
  // ghat = G/(S*SC) < s*a/b  <=>  G*b < s*a*S*SC   (use 128-bit)
  __int128 lhs=(__int128)G*b, rhs=(__int128)s*a*(__int128)S*SC;
  printf("argmax state %llu (c=%llu,b1=%llu)\n",(unsigned long long)Gx,(unsigned long long)(Gx>>s),(unsigned long long)(Gx&MS));
  printf("s=%d H=%d slack=%d chains=%llu  GNUM=%lld  ghat=%.6f per-bit=%.6f  rational bound s*a/b=%.6f  PASS=%d\n",
    s,H,SLACK,(unsigned long long)w,(long long)G,(double)G/((double)S*SC),(double)G/((double)S*SC)/s,(double)s*a/b, lhs<rhs);
  return 0;
}
