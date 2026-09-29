// Exact representability test for single n (p,q coprime, q prime), via the recursion
// "the term with the smallest q-power has the largest p-power":
//   rep(m, A): strip q's from m; for a < A with p^a <= m: if p^a == m -> yes;
//              else if q | (m - p^a) and rep(m - p^a, a) -> yes.
// (The smallest-b term has b = v_q(m); it must have the largest a; the rest is a representation
//  of m - q^b p^a with larger b and smaller a, and its smallest b exceeds b iff q | (m/q^b - p^a).)
// Modes:  repdfs p q check L                        -> compare with brute force for all n < 2^L
//         repdfs p q mc L samples seed [nodelimit]  -> random n in [2^(L-1), 2^L): fraction representable
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>
typedef unsigned __int128 u128; typedef unsigned long long u64;
static int P, Q; static u128 pw[130]; static int npw; static long LIMIT; static __thread long nodes;

static int dfs(u128 m, int A) {
  if (++nodes > LIMIT) return -1;
  while (m % Q == 0) m /= Q;
  int a = A - 1; if (a > npw - 1) a = npw - 1;
  while (a >= 0 && pw[a] > m) a--;
  for (; a >= 0; a--) {
    if (pw[a] == m) return 1;
    u128 r = m - pw[a];
    if (r % Q) continue;
    int res = dfs(r, a);
    if (res) return res;
  }
  return 0;
}

static u64 s[2];
static u64 rnd(void) { u64 x = s[0], y = s[1]; s[0] = y; x ^= x << 23; s[1] = x ^ y ^ (x >> 17) ^ (y >> 26); return s[1] + y; }

static unsigned char *R; static u64 X;
static void brute(u64 sum, int amin, int bmax) {   // terms in order: a strictly up, b strictly down
  u64 pa = 1; for (int i = 0; i < amin; i++) { if (pa > X / P) return; pa *= P; }
  for (int a = amin;; a++) {
    if (pa >= X) break;
    u64 t = pa;
    for (int b = 0; b <= bmax; b++) {
      if (t >= X - sum) break;
      u64 s2 = sum + t; R[s2] = 1;
      if (b > 0) brute(s2, a + 1, b - 1);
      if (t > X / Q) break; t *= Q;
    }
    if (pa > X / P) break; pa *= P;
  }
}

int main(int argc, char **argv) {
  P = atoi(argv[1]); Q = atoi(argv[2]);
  pw[0] = 1; npw = 1;
  while (npw < 128) { u128 nx = pw[npw - 1] * P; if (nx / P != pw[npw - 1] || (nx >> 126)) break; pw[npw++] = nx; }
  if (!strcmp(argv[3], "check")) {
    int L = atoi(argv[4]); X = 1ULL << L; R = calloc(X, 1); brute(0, 0, 64);
    long bad = 0, cnt = 0; LIMIT = 1L << 60;
    for (u64 n = 1; n < X; n++) {
      nodes = 0; int r = dfs(n, 1000); cnt += R[n];
      if (r != R[n]) { if (bad < 5) printf("MISMATCH n=%llu dfs=%d brute=%d\n", n, r, R[n]); bad++; }
    }
    printf("(%d,%d) check L=%d: %ld mismatches, %ld representable below 2^%d\n", P, Q, L, bad, cnt, L);
    return 0;
  }
  int L = atoi(argv[4]); long S = atol(argv[5]); u64 seed = (u64)atoll(argv[6]);
  LIMIT = argc > 7 ? atol(argv[7]) : 20000000;
  long yes = 0, no = 0, und = 0; double tn = 0; long maxn = 0; double t0 = omp_get_wtime();
  #pragma omp parallel reduction(+:yes,no,und,tn) reduction(max:maxn)
  {
    u64 st[2]; st[0] = seed * 0x9E3779B97F4A7C15ULL + 1 + 7919ULL * omp_get_thread_num(); st[1] = 0xD1B54A32D192ED03ULL ^ (u64)omp_get_thread_num();
    #define RND() ({ u64 x_ = st[0], y_ = st[1]; st[0] = y_; x_ ^= x_ << 23; st[1] = x_ ^ y_ ^ (x_ >> 17) ^ (y_ >> 26); st[1] + y_; })
    for (int i = 0; i < 20; i++) (void)RND();
    #pragma omp for schedule(dynamic, 16)
    for (long i = 0; i < S; i++) {
      u128 n = ((u128)RND() << 64) | RND();
      n &= (((u128)1) << L) - 1; n |= ((u128)1) << (L - 1);
      nodes = 0; int r = dfs(n, 1000); tn += nodes; if (nodes > maxn) maxn = nodes;
      if (r == 1) yes++; else if (r == 0) no++; else und++;
    }
  }
  double el = omp_get_wtime() - t0;
  double f = (double)yes / (yes + no);
  printf("(%d,%d) L=%d samples=%ld rep=%ld non=%ld undecided=%ld frac=%.4f +- %.4f  frac*L=%.3f  avg_nodes=%.0f max_nodes=%ld  %.1fs\n",
         P, Q, L, S, yes, no, und, f, 2 * __builtin_sqrt(f * (1 - f) / (yes + no)), f * L, tn / S, maxn,
         el);
  return 0;
}
