// verifyd: exact checker for a D-digit-state / s-digit-block potential certificate with dead states.
// Written independently of gvid.c (different chain enumeration, inverse, transition formula).
// Pair: digits in base B, other base Q (gcd = 1). Blocks of s digits (P = B^s), state = D digits.
// Chains: pairs (alpha-subset of [0,s), gamma-subset of [0,H)) of equal size, paired in increasing order;
//   v = sum B^alpha Q^{-gamma} (mod B^(D+s)), h = max gamma + 1; residue class c = v mod P.
//   Kept chains per class: h <= (min h in class) + SLACK   (same rule as the search).
// Transition from state x in Z/B^D with fresh block u in Z/P using chain C (v = x mod P required):
//   z = x + B^D u,  r = (z - v) mod B^(D+s) (divisible by P),  next = Q^h (r / P) mod B^D.
// Viable set W = largest set of covered states such that (i) for every x in W and every u some kept chain
//   leads into W, and (ii) Q x mod B^D is in W (padded steps multiply the state by Q).
// Certificate check (integers, V scaled by 2^20 and rounded half away from zero):
//   for every x in W:  sum_u min_{C: next in W} [ h 2^20 + Vi(next) ]  -  P Vi(x)  <=  GNUM.
// Reports GNUM, ghat = GNUM / (P 2^20), and PASS iff ghat < s*a/b with Q^a < B^b (checked exactly).
// V file: float32, "transposed" layout of gvid: index (x mod B^(D-s)) * P + x / B^(D-s).
// usage: verifyd B Q s D H SLACK Vfile a b [Wout (bitset, standard layout)] [probe-states-file]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64; typedef int64_t i64; typedef unsigned __int128 u128;
static u64 B, Q, P, MD, MDs, MDm; static int s, D, H;
static u64 mm(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
int main(int argc, char **argv) {
  if (argc < 10) { fprintf(stderr, "usage\n"); return 2; }
  B = atoll(argv[1]); Q = atoll(argv[2]); s = atoi(argv[3]); D = atoi(argv[4]); H = atoi(argv[5]);
  int SLACK = atoi(argv[6]); const char *vf = argv[7]; long a = atol(argv[8]), b = atol(argv[9]);
  P = 1; for (int i = 0; i < s; i++) P *= B;
  MD = 1; for (int i = 0; i < D; i++) MD *= B;
  MDs = MD * P; MDm = MD / P;
  // Q^{-1} mod B^(D+s): brute force mod B, then Newton x <- x (2 - Q x) (precision doubles in the B-adic sense)
  u64 x0 = 0; for (u64 t = 1; t < B; t++) if ((Q * t) % B == 1) { x0 = t; break; }
  if (!x0) { fprintf(stderr, "Q not invertible mod B\n"); return 1; }
  u64 qi = x0; for (int it = 0; it < 8; it++) qi = mm(qi, (2 + MDs - mm(Q % MDs, qi, MDs)) % MDs, MDs);
  if (mm(Q % MDs, qi, MDs) != 1) { fprintf(stderr, "inverse failed\n"); return 1; }
  u64 *qig = malloc(8 * (H + 1)); qig[0] = 1; for (int g = 1; g <= H; g++) qig[g] = mm(qig[g - 1], qi, MDs);
  u64 Bpow[64]; Bpow[0] = 1; for (int i = 1; i < 64; i++) Bpow[i] = Bpow[i - 1] * B;
  // enumerate chains by subset pairs
  u64 capc = 1 << 16, nc = 0; u64 *cv = malloc(8 * capc); int *chh = malloc(4 * capc);
  for (u64 am = 0; am < (1ULL << s); am++) for (u64 gm = 0; gm < (1ULL << H); gm++) {
    if (__builtin_popcountll(am) != __builtin_popcountll(gm)) continue;
    u64 v = 0, A = am, G = gm; int h = 0;
    while (A) { int al = __builtin_ctzll(A), ga = __builtin_ctzll(G); v = (v + mm(Bpow[al], qig[ga], MDs)) % MDs; h = ga + 1; A &= A - 1; G &= G - 1; }
    if (nc == capc) { capc *= 2; cv = realloc(cv, 8 * capc); chh = realloc(chh, 4 * capc); }
    cv[nc] = v; chh[nc] = h; nc++;
  }
  // per class: min h, keep rule
  int *mh = malloc(4 * P); for (u64 c = 0; c < P; c++) mh[c] = 1 << 20;
  for (u64 i = 0; i < nc; i++) { u64 c = cv[i] % P; if (chh[i] < mh[c]) mh[c] = chh[i]; }
  u64 *off = calloc(P + 1, 8); for (u64 i = 0; i < nc; i++) { u64 c = cv[i] % P; if (chh[i] <= mh[c] + SLACK) off[c + 1]++; }
  for (u64 c = 0; c < P; c++) off[c + 1] += off[c];
  u64 nk = off[P]; u64 *kv = malloc(8 * nk); int *kh = malloc(4 * nk); u64 *fill = malloc(8 * P); memcpy(fill, off, 8 * P);
  for (u64 i = 0; i < nc; i++) { u64 c = cv[i] % P; if (chh[i] <= mh[c] + SLACK) { kv[fill[c]] = cv[i]; kh[fill[c]] = chh[i]; fill[c]++; } }
  u64 unc = 0; for (u64 c = 0; c < P; c++) if (off[c + 1] == off[c]) unc++;
  u64 *qh = malloc(8 * (H + 2)); qh[0] = 1; for (int i = 1; i <= H + 1; i++) qh[i] = mm(qh[i - 1], Q, MD);
  fprintf(stderr, "chains total %llu kept %llu, uncovered classes %llu of %llu\n", (unsigned long long)nc,
          (unsigned long long)nk, (unsigned long long)unc, (unsigned long long)P);
  #define NEXT(x, u, j) ({ u64 z_ = (x) + MD * (u); u64 r_ = (z_ + MDs - kv[j]) % MDs; \
      if (r_ % P) { fprintf(stderr, "divisibility failure\n"); exit(1); } mm(qh[kh[j]], (r_ / P) % MD, MD); })
  // viable set (standard layout)
  unsigned char *W = malloc(MD);
  for (u64 x = 0; x < MD; x++) W[x] = off[x % P + 1] > off[x % P];
  for (int pass = 0;; pass++) {
    long rem = 0;
    #pragma omp parallel for schedule(dynamic, 1024) reduction(+:rem)
    for (u64 x = 0; x < MD; x++) {
      if (!W[x]) continue;
      u64 c = x % P; int ok = 1;
      for (u64 u = 0; u < P && ok; u++) {
        int f = 0; for (u64 j = off[c]; j < off[c + 1] && !f; j++) if (W[NEXT(x, u, j)]) f = 1;
        if (!f) ok = 0;
      }
      if (ok && !W[mm(x, Q % MD, MD)]) ok = 0;
      if (!ok) { W[x] = 0; rem++; }
    }
    u64 nw = 0; for (u64 x = 0; x < MD; x++) nw += W[x];
    fprintf(stderr, "viable pass %d: removed %ld, |W| = %llu of %llu\n", pass, rem, (unsigned long long)nw, (unsigned long long)MD);
    if (!rem) break;
  }
  if (argc > 10) { FILE *wf = fopen(argv[10], "wb"); u64 nb = (MD + 7) / 8; unsigned char *bs = calloc(nb, 1);
    for (u64 x = 0; x < MD; x++) if (W[x]) bs[x >> 3] |= 1 << (x & 7); fwrite(bs, 1, nb, wf); fclose(wf); free(bs); }
  // V table
  float *Vf = malloc(4 * MD); FILE *f = fopen(vf, "rb");
  if (!f || fread(Vf, 4, MD, f) != MD) { fprintf(stderr, "read V failed\n"); return 1; } fclose(f);
  const i64 SC = 1LL << 20;
  u64 *probe = NULL; int np = 0;
  if (argc > 11) { FILE *pf = fopen(argv[11], "r"); probe = malloc(8 * 100000); unsigned long long qq;
    while (np < 100000 && fscanf(pf, "%llu", &qq) == 1) probe[np++] = qq; fclose(pf); }
  #define VI(x) ({ double d_ = ldexp((double)Vf[((x) % MDm) * P + (x) / MDm], 20); double r_ = floor(fabs(d_) + 0.5); (i64)(d_ < 0 ? -r_ : r_); })
  i64 G = INT64_MIN; u64 Gx = 0; long bad = 0; i64 vmax = INT64_MIN, vmin = INT64_MAX; u64 nw = 0;
  #pragma omp parallel
  { i64 lg = INT64_MIN; u64 lx = 0; i64 lvmax = INT64_MIN, lvmin = INT64_MAX;
    #pragma omp for schedule(dynamic, 1024) reduction(+:bad,nw)
    for (u64 x = 0; x < MD; x++) {
      if (!W[x]) continue; nw++;
      u64 c = x % P; i64 tot = 0; i64 vx = VI(x);
      if (!(fabs((double)Vf[(x % MDm) * P + x / MDm]) < 1e5)) { bad++; continue; }
      if (vx > lvmax) lvmax = vx; if (vx < lvmin) lvmin = vx;
      for (u64 u = 0; u < P; u++) {
        i64 best = INT64_MAX;
        for (u64 j = off[c]; j < off[c + 1]; j++) { u64 nx = NEXT(x, u, j); if (!W[nx]) continue;
          i64 val = (i64)kh[j] * SC + VI(nx); if (val < best) best = val; }
        if (best == INT64_MAX) { bad++; best = 0; }
        tot += best;
      }
      i64 d = tot - (i64)P * vx; if (d > lg) { lg = d; lx = x; }
      if (probe) for (int q = 0; q < np; q++) if (probe[q] == x) {
        #pragma omp critical
        printf("probe state %llu d=%lld\n", (unsigned long long)x, (long long)d); }
    }
    #pragma omp critical
    { if (lg > G) { G = lg; Gx = lx; } if (lvmax > vmax) vmax = lvmax; if (lvmin < vmin) vmin = lvmin; }
  }
  u128 Qa = 1, Bb = 1; int ovf = 0; for (long i = 0; i < a; i++) { Qa *= Q; if (Qa >> 120) ovf = 1; } for (long i = 0; i < b; i++) { Bb *= B; if (Bb >> 120) ovf = 1; }
  int ratok = !ovf && Qa < Bb;
  __int128 lhs = (__int128)G * b, rhs = (__int128)s * a * (__int128)P * SC;
  printf("B=%llu Q=%llu s=%d D=%d H=%d slack=%d |W|=%llu (%.6f of states) bad=%ld  GNUM=%lld argmax=%llu  ghat=%.7f  s*a/b=%.7f  Q^a<B^b:%d  osc(V)=%.4f  PASS=%d\n",
         (unsigned long long)B, (unsigned long long)Q, s, D, H, SLACK, (unsigned long long)nw, (double)nw / MD, bad, (long long)G,
         (unsigned long long)Gx, (double)G / ((double)P * SC), (double)s * a / b, ratok, (double)(vmax - vmin) / SC,
         ratok && !bad && lhs < rhs);
  return 0;
}
