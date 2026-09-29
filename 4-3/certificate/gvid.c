// gvid: look-ahead value iteration with a D-digit state and s-digit blocks (general base, dead states).
// Pair (B-adic digits, other base Q). M = B^s (block), state x in Z/B^D (D >= s) = next D digits of the
// normalised residual (x mod M = current block c). Fresh u in Z/M enters as the top s digits.
// Chains: {(alpha,gamma)} strictly increasing, alpha < s, gamma < H; v = sum B^alpha Q^{-gamma} mod B^{D+s};
// h = max gamma + 1; usable at x iff v = c (mod M). Exact transition:
//   w = ((x - v) mod B^{D+s}) / M,  base = Q^h w mod B^D,
//   next(u) = low + B^{D-s} * ((t0 + Q^h u) mod M),  low = base mod B^{D-s}, t0 = base / B^{D-s}.
// Memory layout: V stored as T[low*M + t] for x = low + B^{D-s} t, so each chain's update reads one
// contiguous row of M floats. Viable set W (closed under all u) computed first; residues without chains
// are dead; W is also closed under x -> Q x (needed for padded steps). Prints the value-iteration bracket and its ratio to s*log_Q(B) (need < 1 for a certificate).
// usage: gvid B Q s D H iters SLACK [Vout (transposed layout)]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static u64 mulm(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 invmod(u64 a, u64 m) {
  __int128 t = 0, nt = 1, r = m, nr = a % m;
  while (nr) { __int128 q = r / nr, x; x = t - q * nt; t = nt; nt = x; x = r - q * nr; r = nr; nr = x; }
  if (r != 1) { fprintf(stderr, "not invertible\n"); exit(1); }
  if (t < 0) t += m; return (u64)t;
}
typedef struct { u64 v; int h; } Ch;
static Ch *ch; static u64 nch = 0, cap = 0;
static int s, D, H; static u64 B, Q, M, Mk, Mk1, Mkm1;
static u64 Bp[64], uq[64];
static void gen(int a0, int g0, u64 v, int h) {
  if (nch == cap) { cap = cap ? cap * 2 : 1 << 20; ch = realloc(ch, cap * sizeof(Ch)); }
  ch[nch].v = v; ch[nch].h = h; nch++;
  for (int a = a0; a < s; a++) for (int g = g0; g < H; g++) gen(a + 1, g + 1, (v + mulm(uq[g], Bp[a], Mk1)) % Mk1, g + 1);
}
static int cmpc(const void *a, const void *b) { u64 x = ((Ch *)a)->v % M, y = ((Ch *)b)->v % M; return x < y ? -1 : x > y; }
static inline u64 TI(u64 x) { return (x % Mkm1) * M + x / Mkm1; }  // transposed index
int main(int argc, char **argv) {
  B = atoll(argv[1]); Q = atoll(argv[2]); s = atoi(argv[3]); D = atoi(argv[4]); H = atoi(argv[5]);
  int iters = atoi(argv[6]), SLACK = atoi(argv[7]);
  if (D < s) { fprintf(stderr, "need D >= s\n"); return 1; }
  M = 1; for (int i = 0; i < s; i++) M *= B;
  Mk = 1; for (int i = 0; i < D; i++) Mk *= B;
  Mk1 = Mk * M; Mkm1 = Mk / M;
  if (Mk1 / M != Mk) { fprintf(stderr, "overflow\n"); return 1; }
  Bp[0] = 1; for (int i = 1; i < s; i++) Bp[i] = Bp[i - 1] * B;
  u64 qinv = invmod(Q, Mk1); uq[0] = 1; for (int g = 1; g <= H; g++) uq[g] = mulm(uq[g - 1], qinv, Mk1);
  gen(0, 0, 0, 0);
  qsort(ch, nch, sizeof(Ch), cmpc);
  u64 *cnt = calloc(M + 1, 8); for (u64 i = 0; i < nch; i++) cnt[ch[i].v % M + 1]++;
  for (u64 c = 0; c < M; c++) cnt[c + 1] += cnt[c];
  unsigned char *cov = calloc(M, 1); u64 unc = 0; double flat = 0;
  { u64 w = 0; u64 *nc = calloc(M + 1, 8);
    for (u64 c = 0; c < M; c++) {
      int mh = 1 << 20; for (u64 j = cnt[c]; j < cnt[c + 1]; j++) if (ch[j].h < mh) mh = ch[j].h;
      cov[c] = cnt[c + 1] > cnt[c]; if (!cov[c]) unc++; else flat += mh;
      nc[c] = w; for (u64 j = cnt[c]; j < cnt[c + 1]; j++) if (ch[j].h <= mh + SLACK) ch[w++] = ch[j];
    }
    nc[M] = w; memcpy(cnt, nc, 8 * (M + 1)); }
  flat /= (double)(M - unc);
  u64 *pq = malloc(8 * (H + 2)); pq[0] = 1; for (int i = 1; i <= H + 1; i++) pq[i] = mulm(pq[i - 1], Q, Mk1);
  double need = s * log((double)B) / log((double)Q);
  printf("B=%llu Q=%llu s=%d D=%d window=%d M=%llu states=%llu H=%d slack=%d chains=%llu uncovered=%llu/%llu flat=%.4f need<%.5f\n",
         (unsigned long long)B, (unsigned long long)Q, s, D, D + s, (unsigned long long)M, (unsigned long long)Mk, H, SLACK,
         (unsigned long long)cnt[M], (unsigned long long)unc, (unsigned long long)M, flat, need); fflush(stdout);
  // alive in transposed layout
  unsigned char *alive = malloc(Mk);
  for (u64 x = 0; x < Mk; x++) alive[TI(x)] = cov[x % M];
  for (int pass = 0;; pass++) {
    long removed = 0;
    #pragma omp parallel reduction(+:removed)
    { unsigned char *ok = malloc(M);
      #pragma omp for schedule(dynamic, 256)
      for (u64 x = 0; x < Mk; x++) {
        if (!alive[TI(x)]) continue;
        u64 c = x % M; memset(ok, 0, M); u64 nok = 0;
        for (u64 j = cnt[c]; j < cnt[c + 1] && nok < M; j++) {
          int h = ch[j].h; u64 w = ((x + Mk1 - ch[j].v) % Mk1) / M; u64 base = mulm(pq[h] % Mk, w, Mk);
          u64 low = base % Mkm1, t = base / Mkm1, m = pq[h] % M; const unsigned char *row = alive + low * M;
          for (u64 u = 0; u < M; u++) { if (!ok[u] && row[t]) { ok[u] = 1; nok++; } t += m; if (t >= M) t -= M; }
        }
        if (nok < M) { alive[TI(x)] = 0; removed++; continue; }
        // padding multiplies the state by Q: the viable set must be closed under x -> Q x
        if (!alive[TI(mulm(x, Q % Mk, Mk))]) { alive[TI(x)] = 0; removed++; }
      }
      free(ok); }
    u64 na = 0; for (u64 i = 0; i < Mk; i++) na += alive[i];
    printf("viable pass %d: removed %ld, alive %llu of %llu\n", pass, removed, (unsigned long long)na, (unsigned long long)Mk); fflush(stdout);
    if (!na) { printf("NO VIABLE STATES\n"); return 0; }
    if (!removed) break;
  }
  const float BIG = 1e6f;
  float *V = calloc(Mk, 4), *NV = malloc(Mk * 4);   // transposed layout
  for (u64 i = 0; i < Mk; i++) if (!alive[i]) V[i] = BIG;
  for (int it = 0; it < iters; it++) {
    #pragma omp parallel
    { float *best = malloc(M * 4);
      #pragma omp for schedule(dynamic, 256)
      for (u64 x = 0; x < Mk; x++) {
        u64 ix = TI(x);
        if (!alive[ix]) { NV[ix] = BIG; continue; }
        u64 c = x % M;
        for (u64 u = 0; u < M; u++) best[u] = 1e30f;
        for (u64 j = cnt[c]; j < cnt[c + 1]; j++) {
          int h = ch[j].h; u64 w = ((x + Mk1 - ch[j].v) % Mk1) / M; u64 base = mulm(pq[h] % Mk, w, Mk);
          u64 low = base % Mkm1, t = base / Mkm1, m = pq[h] % M; const float *row = V + low * M; float hh = (float)h;
          for (u64 u = 0; u < M; u++) { float v = hh + row[t]; if (v < best[u]) best[u] = v; t += m; if (t >= M) t -= M; }
        }
        double tot = 0; for (u64 u = 0; u < M; u++) tot += best[u]; NV[ix] = (float)(tot / M);
      }
      free(best); }
    double mn = 1e18, mx = -1e18; u64 b0 = 0; while (!alive[b0]) b0++;
    for (u64 i = 0; i < Mk; i++) { if (!alive[i]) continue; double d = NV[i] - V[i]; if (d < mn) mn = d; if (d > mx) mx = d; }
    float base0 = NV[b0]; for (u64 i = 0; i < Mk; i++) V[i] = alive[i] ? NV[i] - base0 : BIG;
    if (argc > 8) { FILE *f = fopen(argv[8], "wb"); fwrite(V, 4, Mk, f); fclose(f); }
    printf("it=%d g in [%.5f, %.5f]  ratio-to-need [%.4f, %.4f]\n", it, mn, mx, mn / need, mx / need); fflush(stdout);
  }
  return 0;
}
