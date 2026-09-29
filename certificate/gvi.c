// General-base two-block look-ahead value iteration (look4.c generalised, 2026-09-28).
// Pair (B-adic blocks, other base Q): chains {(alpha,gamma)} strictly increasing, alpha<s, gamma<H,
// v = sum B^alpha Q^{-gamma} mod M^3 (M = B^s); h = max gamma + 1.  Target: average h per block < s*log_Q B.
// State (c,b1) in (Z/M)^2, fresh u; z = c + M b1 + M^2 u; next = Q^h ((z - v) mod M^3)/M mod M^2.
// With v = c + M k1 + M^2 k2:  d1 = (b1-k1) mod M, borrow = [b1<k1], c' = Q^h d1 mod M, q1 = floor(Q^h d1/M) mod M,
//   b1' = q1 + Q^h (u - k2 - borrow) mod M = Q^h (u + off), off = q1 Q^{-h} - k2 - borrow.
// Prints the value-iteration bracket [min, max] of (T V - V): min is a rigorous lower bound on the optimal
// average cost of this MDP (fixed chain set), max an upper bound (up to float rounding).
// usage: gvi B Q s H iters SLACK [outV]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
int s,H,SLACK; u64 B,Q,M,M3;
typedef struct { u64 k1,k2; int h; } Ch;
Ch *ch; u64 nch=0,cap=0; u64 *res; u64 *uq;
static u64 mulm(u64 a,u64 b,u64 m){ return (u64)((u128)a*b%m); }
void add(u64 v,int h){ if(nch==cap){cap=cap?cap*2:1<<20; ch=realloc(ch,cap*sizeof(Ch)); res=realloc(res,cap*8);}
  ch[nch].k1=(v/M)%M; ch[nch].k2=(v/M/M)%M; ch[nch].h=h; res[nch]=v%M; nch++; }
u64 Bp[64];
void gen(int a0,int g0,u64 v,int h){ add(v,h);
  for(int a=a0;a<s;a++) for(int g=g0;g<H;g++) gen(a+1,g+1,(v+mulm(uq[g],Bp[a],M3))%M3,g+1); }
// inverse of Q mod m (Q coprime to m) by extended Euclid
u64 invmod(u64 a,u64 m){ __int128 t=0,nt=1,r=m,nr=a%m; while(nr){ __int128 q=r/nr,x; x=t-q*nt;t=nt;nt=x; x=r-q*nr;r=nr;nr=x; } if(r!=1){fprintf(stderr,"not invertible\n");exit(1);} if(t<0)t+=m; return (u64)t; }
int main(int argc,char**argv){
  B=atoll(argv[1]); Q=atoll(argv[2]); s=atoi(argv[3]); H=atoi(argv[4]); int iters=atoi(argv[5]); SLACK=atoi(argv[6]);
  M=1; for(int i=0;i<s;i++) M*=B; M3=M*M*M; if(M3/M/M!=M){ fprintf(stderr,"overflow\n"); return 1; }
  Bp[0]=1; for(int i=1;i<s;i++) Bp[i]=Bp[i-1]*B;
  u64 qinv=invmod(Q,M3);
  uq=malloc(8*(H+1)); uq[0]=1; for(int g=1;g<=H;g++) uq[g]=mulm(uq[g-1],qinv,M3);
  gen(0,0,0,0);
  u64 *cnt=calloc(M+1,8); for(u64 i=0;i<nch;i++) cnt[res[i]+1]++; for(u64 c=0;c<M;c++) cnt[c+1]+=cnt[c];
  Ch *bk=malloc(nch*sizeof(Ch)); u64 *pos=malloc(8*M); memcpy(pos,cnt,8*M);
  for(u64 i=0;i<nch;i++) bk[pos[res[i]]++]=ch[i];
  u64 unc=0; for(u64 c=0;c<M;c++) if(cnt[c+1]==cnt[c]) unc++;
  if(unc){ fprintf(stderr,"%llu residues uncovered (of %llu)\n",(unsigned long long)unc,(unsigned long long)M); return 1; }
  double flat=0;
  { u64 w=0; u64 *nc=calloc(M+1,8);
    for(u64 c=0;c<M;c++){ int mh=99; for(u64 j=cnt[c];j<cnt[c+1];j++) if(bk[j].h<mh) mh=bk[j].h; flat+=mh;
      nc[c]=w; for(u64 j=cnt[c];j<cnt[c+1];j++) if(bk[j].h<=mh+SLACK) bk[w++]=bk[j]; }
    nc[M]=w; memcpy(cnt,nc,8*(M+1)); fprintf(stderr,"chains after prune: %llu (%.1f/res)\n",(unsigned long long)w,(double)w/M); }
  flat/=M;
  u64 *pq=malloc(8*(H+2)); pq[0]=1; for(int i=1;i<=H+1;i++) pq[i]=pq[i-1]*Q;      // exact, small
  u64 qim=invmod(Q,M); u64 *iq=malloc(8*(H+2)); iq[0]=1; for(int i=1;i<=H+1;i++) iq[i]=mulm(iq[i-1],qim,M);
  float *V=calloc(M*M,4), *NV=malloc(M*M*4);
  float *W=malloc((size_t)(H+1)*M*M*4); // W[h][c'][w] = V[c'][Q^h w mod M]
  double need=s*log((double)B)/log((double)Q);
  printf("B=%llu Q=%llu s=%d M=%llu H=%d slack=%d flat(min-height avg)=%.5f need<%.5f\n",(unsigned long long)B,(unsigned long long)Q,s,(unsigned long long)M,H,SLACK,flat,need);
  for(int it=0;it<iters;it++){
    #pragma omp parallel for schedule(static)
    for(u64 cp=0;cp<M;cp++) for(int h=0;h<=H;h++){ u64 m=pq[h]%M; float *dst=W+((size_t)h*M+cp)*M; const float *src=V+cp*M;
      for(u64 w=0;w<M;w++) dst[w]=src[mulm(w,m,M)]; }
    #pragma omp parallel
    { float *best=malloc(M*4);
      #pragma omp for schedule(dynamic,16)
      for(u64 st=0;st<M*M;st++){
        u64 c=st/M, b1=st%M;
        for(u64 x=0;x<M;x++) best[x]=1e30f;
        for(u64 j=cnt[c];j<cnt[c+1];j++){
          int h=bk[j].h; u64 k1=bk[j].k1,k2=bk[j].k2;
          u64 d1=(b1+M-k1)%M; u64 borrow=(b1<k1); u128 prod=(u128)pq[h]*d1; u64 cp=(u64)(prod%M), q1=(u64)((prod/M)%M);
          u64 off=(mulm(q1,iq[h],M)+2*M-k2-borrow)%M;
          const float *row=W+((size_t)h*M+cp)*M; float hh=(float)h;
          u64 split=M-off; // x+off < M for x<split
          for(u64 x=0;x<split;x++){ float v=hh+row[x+off]; if(v<best[x]) best[x]=v; }
          for(u64 x=split;x<M;x++){ float v=hh+row[x+off-M]; if(v<best[x]) best[x]=v; }
        }
        double tot=0; for(u64 x=0;x<M;x++) tot+=best[x]; NV[st]=(float)(tot/M);
      }
      free(best); }
    double mn=1e18,mx=-1e18; for(u64 x=0;x<M*M;x++){ double d=NV[x]-V[x]; if(d<mn)mn=d; if(d>mx)mx=d; }
    float base=NV[0]; for(u64 x=0;x<M*M;x++) V[x]=NV[x]-base;
    if(argc>7){ FILE*f=fopen(argv[7],"wb"); fwrite(V,4,M*M,f); fclose(f); }
    printf("it=%d g in [%.5f, %.5f]  ratio-to-need [%.4f, %.4f]\n",it,mn,mx,mn/need,mx/need); fflush(stdout);
  }
  return 0;
}
