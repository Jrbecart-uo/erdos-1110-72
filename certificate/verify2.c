// Second, independently written FULL-STATE checker for the (7,2) two-block look-ahead certificate
// (2026-09-28 recheck). Deliberately different from verify.c:
//  - chains enumerated as (alpha-subset bitmask, gamma-subset bitmask) of equal popcount, paired sorted;
//  - 7^{-1} mod 2^64 computed as 7^(2^62-1) (exponent of (Z/2^64)^* is 2^62), not by Newton;
//  - chain values kept as full 64-bit 2-adic integers; each transition uses a 64-bit z whose bits above 3s
//    are pseudo-random (they must not matter), z' = 7^h * ((z - v) >> s) mod 2^64;
//  - V rounded by floor(|d|+1/2) with sign (= llround, half away from zero), d = V*2^20 exact in double.
// Checks for every state x=(c,b1): sum_u min_C [h*2^20 + Vi(next)] - 2^s*Vi(x) <= GNUM; prints GNUM, argmax,
// and a checksum of the full per-state d vector.
// usage: verify2 s H SLACK V.bin a b      (a/b <= log_7 2 needs 7^a < 2^b, checked here with 128-bit ints)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef uint64_t u64; typedef int64_t i64; typedef unsigned __int128 u128;
static u64 powmod64(u64 b, u64 e){ u64 r=1; while(e){ if(e&1) r*=b; b*=b; e>>=1; } return r; }
static u64 mix(u64 x){ x+=0x9e3779b97f4a7c15ULL; x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL; x=(x^(x>>27))*0x94d049bb133111ebULL; return x^(x>>31); }
int main(int argc,char**argv){
  if(argc<7){ fprintf(stderr,"usage\n"); return 2; }
  int s=atoi(argv[1]), H=atoi(argv[2]), SL=atoi(argv[3]); long a=atol(argv[5]), b=atol(argv[6]);
  u64 S=1ULL<<s, MS=S-1;
  u64 inv7=powmod64(7,(1ULL<<62)-1); if(inv7*7!=1){ fprintf(stderr,"inv7\n"); return 1; }
  u64 ip[64]; ip[0]=1; for(int g=1;g<H;g++) ip[g]=ip[g-1]*inv7;
  // enumerate chains
  u64 cap=1<<22, n=0; u64 *cv=malloc(8*cap); int *chh=malloc(4*cap);
  for(u64 am=0; am<S; am++) for(u64 gm=0; gm<(1ULL<<H); gm++){
    if(__builtin_popcountll(am)!=__builtin_popcountll(gm)) continue;
    u64 v=0, A=am, G=gm; int h=0;
    while(A){ int al=__builtin_ctzll(A), ga=__builtin_ctzll(G); v+=ip[ga]<<al; h=ga+1; A&=A-1; G&=G-1; }
    if(n==cap){ fprintf(stderr,"cap\n"); return 1; } cv[n]=v; chh[n]=h; n++;
  }
  // bucket by residue, prune to h <= min_h + SL
  int *mh=malloc(4*S); for(u64 c=0;c<S;c++) mh[c]=1<<20;
  for(u64 i=0;i<n;i++){ u64 c=cv[i]&MS; if(chh[i]<mh[c]) mh[c]=chh[i]; }
  for(u64 c=0;c<S;c++) if(mh[c]==1<<20){ fprintf(stderr,"uncovered %llu\n",(unsigned long long)c); return 1; }
  u64 *off=calloc(S+1,8); for(u64 i=0;i<n;i++) if(chh[i]<=mh[cv[i]&MS]+SL) off[(cv[i]&MS)+1]++;
  for(u64 c=0;c<S;c++) off[c+1]+=off[c];
  u64 m=off[S]; u64 *pv=malloc(8*m); int *ph=malloc(4*m); u64 *fill=malloc(8*S); for(u64 c=0;c<S;c++) fill[c]=off[c];
  for(u64 i=0;i<n;i++){ u64 c=cv[i]&MS; if(chh[i]<=mh[c]+SL){ pv[fill[c]]=cv[i]; ph[fill[c]]=chh[i]; fill[c]++; } }
  fprintf(stderr,"all chains %llu, kept %llu\n",(unsigned long long)n,(unsigned long long)m);
  // V table
  float *V=malloc(4*S*S); FILE*f=fopen(argv[4],"rb"); if(!f||fread(V,4,S*S,f)!=S*S){ fprintf(stderr,"V\n"); return 1; } fclose(f);
  i64 *Vi=malloc(8*S*S);
  for(u64 x=0;x<S*S;x++){ double d=ldexp((double)V[x],20); if(!(fabs(d)<1e15)){ fprintf(stderr,"bad V\n"); return 1; }
    double r=floor(fabs(d)+0.5); Vi[x]=(i64)(d<0?-r:r); }
  u64 p7[64]; p7[0]=1; for(int i=1;i<=H;i++) p7[i]=p7[i-1]*7;
  i64 *D=malloc(8*S*S);
  #pragma omp parallel for schedule(dynamic,256)
  for(u64 x=0;x<S*S;x++){
    u64 c=x>>s, b1=x&MS; i64 tot=0;
    for(u64 u=0;u<S;u++){
      u64 z=c|(b1<<s)|(u<<(2*s))|(mix(x*S+u)<<(3*s));
      i64 best=INT64_MAX;
      for(u64 j=off[c];j<off[c+1];j++){
        u64 zp=p7[ph[j]]*((z-pv[j])>>s);          // exact mod 2^(64-s) >= 2^(2s)
        i64 val=(i64)ph[j]*(1LL<<20)+Vi[((zp&MS)<<s)|((zp>>s)&MS)];
        if(val<best) best=val;
      }
      tot+=best;
    }
    D[x]=tot-(i64)S*Vi[x];
  }
  i64 G=D[0]; u64 gx=0; u64 cks=0; for(u64 x=0;x<S*S;x++){ if(D[x]>G){G=D[x];gx=x;} cks=mix(cks^(u64)D[x]); }
  u128 p7a=1, p2b=(u128)1<<b; for(long i=0;i<a;i++) p7a*=7;
  int ratok=(b<127)&&(p7a<p2b);
  __int128 lhs=(__int128)G*b, rhs=(__int128)s*a*(__int128)S*(1LL<<20);
  printf("s=%d H=%d slack=%d kept=%llu GNUM=%lld argmax=%llu (c=%llu,b1=%llu) dchecksum=%016llx\n",s,H,SL,(unsigned long long)m,(long long)G,
    (unsigned long long)gx,(unsigned long long)(gx>>s),(unsigned long long)(gx&MS),(unsigned long long)cks);
  printf("ghat=%.7f  s*a/b=%.7f  7^a<2^b:%d  PASS=%d\n",(double)G/((double)S*(1<<20)),(double)s*a/b,ratok,ratok&&(lhs<rhs));
  return 0;
}
