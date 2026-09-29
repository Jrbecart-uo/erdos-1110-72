// Exact two-block lookahead MDP for (7,2).
// Chain C: alpha<s strict, gamma<H strict; v = sum 2^alpha 7^{-gamma} mod 2^{3s}; c=v mod S, k1=(v>>s)&MS, k2=(v>>2s)&MS, h.
// State (c,b1): c = current normalized block residue, b1 = next block bits in current frame. Fresh u = block-after-next raw bits.
// Next state: d1=(b1-k1)&MS, borrow=[b1<k1]; c'=(7^h d1)&MS; q1=(7^h d1)>>s; b2'=(7^h*(u-k2-borrow)+q1)&MS.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
int s,H,SLACK; u64 S,MS,M3;
typedef struct { u64 k1,k2; int h; } Ch;
Ch *ch; u64 nch=0,cap=0; u64 *res; u64 *u7;
void add(u64 v,int h){ if(nch==cap){cap=cap?cap*2:1<<20; ch=realloc(ch,cap*sizeof(Ch)); res=realloc(res,cap*8);} 
  ch[nch].k1=(v>>s)&MS; ch[nch].k2=(v>>(2*s))&MS; ch[nch].h=h; res[nch]=v&MS; nch++; }
void gen(int a0,int g0,u64 v,int h){ add(v,h);
  for(int a=a0;a<s;a++) for(int g=g0;g<H;g++){ u64 t=(u7[g]<<a)&(M3-1); gen(a+1,g+1,(v+t)&(M3-1),g+1); } }
int main(int argc,char**argv){
  s=atoi(argv[1]); H=atoi(argv[2]); int iters=atoi(argv[3]); SLACK=atoi(argv[4]);
  S=1ULL<<s; MS=S-1; M3=1ULL<<(3*s);
  u64 pinv=1; { u64 x=7; for(int i=0;i<64;i++) pinv*=(2-x*pinv);} 
  u7=malloc(8*(H+1)); u7[0]=1; for(int g=1;g<=H;g++) u7[g]=(u7[g-1]*pinv)&(M3-1);
  gen(0,0,0,0);
  u64 *cnt=calloc(S+1,8); for(u64 i=0;i<nch;i++) cnt[res[i]+1]++; for(u64 c=0;c<S;c++) cnt[c+1]+=cnt[c];
  Ch *bk=malloc(nch*sizeof(Ch)); u64 *pos=malloc(8*S); memcpy(pos,cnt,8*S);
  for(u64 i=0;i<nch;i++) bk[pos[res[i]]++]=ch[i];
  for(u64 c=0;c<S;c++) if(cnt[c+1]==cnt[c]){ fprintf(stderr,"uncovered %llu\n",(unsigned long long)c); return 1; }
  { u64 w=0; u64 *nc=calloc(S+1,8);
    for(u64 c=0;c<S;c++){ int mh=99; for(u64 j=cnt[c];j<cnt[c+1];j++) if(bk[j].h<mh) mh=bk[j].h;
      nc[c]=w; for(u64 j=cnt[c];j<cnt[c+1];j++) if(bk[j].h<=mh+SLACK) bk[w++]=bk[j]; }
    nc[S]=w; memcpy(cnt,nc,8*(S+1)); fprintf(stderr,"chains after prune: %llu (%.1f/res)\n",(unsigned long long)w,(double)w/S); }
  u64 *p7=malloc(8*(H+2)); p7[0]=1; for(int i=1;i<=H+1;i++) p7[i]=p7[i-1]*7; // exact (small)
  u64 *i7=malloc(8*(H+2)); i7[0]=1; for(int i=1;i<=H+1;i++) i7[i]=(i7[i-1]*pinv)&MS;
  float *V=calloc(S*S,4), *NV=malloc(S*S*4);
  float *W=malloc((size_t)(H+1)*S*S*4); // W[h][c'][w] = V[c'][(7^h w)&MS]
  double mu=log(2)/log(7);
  for(int it=0;it<iters;it++){
    #pragma omp parallel for schedule(static)
    for(u64 cp=0;cp<S;cp++) for(int h=0;h<=H;h++){ u64 m=p7[h]&MS; float *dst=W+((size_t)h*S+cp)*S; const float *src=V+cp*S;
      for(u64 w=0;w<S;w++) dst[w]=src[(w*m)&MS]; }
    #pragma omp parallel
    { float *best=malloc(S*4);
      #pragma omp for schedule(dynamic,16)
      for(u64 st=0;st<S*S;st++){
        u64 c=st>>s, b1=st&MS;
        for(u64 x=0;x<S;x++) best[x]=1e30f;
        for(u64 j=cnt[c];j<cnt[c+1];j++){
          int h=bk[j].h; u64 k1=bk[j].k1,k2=bk[j].k2;
          u64 d1=(b1-k1)&MS; u64 borrow=(b1<k1); u64 prod=p7[h]*d1; u64 cp=prod&MS, q1=prod>>s;
          u64 off=((0-k2-borrow)+q1*i7[h])&MS;
          const float *row=W+((size_t)h*S+cp)*S; float hh=(float)h;
          for(u64 x=0;x<S;x++){ float v=hh+row[(x+off)&MS]; if(v<best[x]) best[x]=v; }
        }
        double tot=0; for(u64 x=0;x<S;x++) tot+=best[x]; NV[st]=(float)(tot/S);
      }
      free(best); }
    double mn=1e18,mx=-1e18; for(u64 x=0;x<S*S;x++){ double d=NV[x]-V[x]; if(d<mn)mn=d; if(d>mx)mx=d; }
    float base=NV[0]; for(u64 x=0;x<S*S;x++) V[x]=NV[x]-base;
    { char fn[64]; sprintf(fn,"V_s%d.bin",s); FILE*f=fopen(fn,"wb"); fwrite(V,4,S*S,f); fclose(f); }
    printf("exact-2look s=%d H=%d it=%d g in [%.5f, %.5f] per-bit [%.5f, %.5f] need < %.5f\n",s,H,it,mn,mx,mn/s,mx/s,mu); fflush(stdout);
  }
  return 0;
}
