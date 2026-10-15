/* zt2: like zt, but phase-1 BFS uses compact 64-bit states (depth d0 <= 62) and phase 2 can be chunked.
   Usage: zt2 a d0 nchunks chunk
   Output: B(a) restricted to this chunk = 1 + deepest surviving depth (all branches die before it). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NW 4
typedef struct { uint64_t w[NW]; } bv;
static inline uint64_t sxor64(uint64_t s) { s ^= s >> 1; s ^= s >> 2; s ^= s >> 4; s ^= s >> 8; s ^= s >> 16; s ^= s >> 32; return s; }
static inline void step(const bv *Dkm1, const bv *Dk, int k, int yk, bv *out) {
  uint64_t g[NW];
  for (int i = 0; i < NW; i++) {
    uint64_t v = Dk->w[i] | Dkm1->w[i];
    int lo = 64 * i;
    if (k <= lo) v = 0; else if (k < lo + 64) v &= (1ULL << (k - lo)) - 1;
    g[i] = v;
  }
  int carry = 0;
  for (int i = NW - 1; i >= 0; i--) {
    uint64_t s = sxor64(g[i]);
    if (carry) s = ~s;
    carry ^= __builtin_parityll(g[i]);
    int lo = 64 * i; uint64_t m;
    if (k <= lo) m = 0; else if (k >= lo + 64) m = ~0ULL; else m = (1ULL << (k - lo)) - 1;
    s &= m; if (yk) s ^= m;
    out->w[i] = s;
  }
  if (yk) out->w[k >> 6] |= 1ULL << (k & 63);
}
static inline uint64_t step64(uint64_t Dkm1, uint64_t Dk, int k, int yk) {
  /* k <= 62 */
  uint64_t m = (k == 0) ? 0 : ((1ULL << k) - 1);
  uint64_t g = (Dk | Dkm1) & m;
  uint64_t s = sxor64(g) & m;
  if (yk) s ^= m;
  if (yk) s |= 1ULL << k;
  return s;
}
typedef struct { uint64_t a, b; } st;
static st *tab; static uint8_t *used; static size_t cap, cnt;
static inline uint64_t hsh(uint64_t a, uint64_t b) { uint64_t h = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL; return h ^ (h >> 31); }
static void hput(uint64_t a, uint64_t b) {
  size_t i = hsh(a, b) & (cap - 1);
  while (used[i]) { if (tab[i].a == a && tab[i].b == b) return; i = (i + 1) & (cap - 1); }
  used[i] = 1; tab[i].a = a; tab[i].b = b; cnt++;
  if (cnt * 2 > cap) { fprintf(stderr, "hash full\n"); exit(1); }
}
static int A, MAXD = 64 * NW - 2;
static long long surv[600];
static int deepest = 0;
static long long nodes = 0;
static void dfs(int k, const bv *Dkm1, const bv *Dk) {
  if (k >= MAXD) { printf("MAXD reached: inconclusive\n"); exit(2); }
  int ny = (k % 2 == 0) ? 1 : 2;
  for (int q = 0; q < ny; q++) {
    int yk = (k % 2 == 0) ? 1 : q;
    bv Dn; step(Dkm1, Dk, k, yk, &Dn); nodes++;
    if (k + 1 >= A && (Dn.w[0] & 1)) continue;
    surv[k + 1]++;
    if (k + 1 > deepest) deepest = k + 1;
    dfs(k + 1, Dk, &Dn);
  }
}
int main(int argc, char **argv) {
  A = atoi(argv[1]); int d0 = atoi(argv[2]);
  int nch = argc > 3 ? atoi(argv[3]) : 1, ch = argc > 4 ? atoi(argv[4]) : 0;
  if (d0 >= A) d0 = A - 1;
  if (d0 > 62) d0 = 62;
  st *cur = malloc(sizeof(st)); size_t ncur = 1; cur[0].a = cur[0].b = 0;
  for (int k = 0; k < d0; k++) {
    cap = 1024; while (cap < 4 * ncur + 16) cap <<= 1;
    tab = malloc(cap * sizeof(st)); used = calloc(cap, 1); cnt = 0;
    if (!tab || !used) { fprintf(stderr, "oom\n"); return 1; }
    for (size_t i = 0; i < ncur; i++) {
      if (k % 2 == 0) hput(cur[i].b, step64(cur[i].a, cur[i].b, k, 1));
      else { hput(cur[i].b, step64(cur[i].a, cur[i].b, k, 0)); hput(cur[i].b, step64(cur[i].a, cur[i].b, k, 1)); }
    }
    free(cur); cur = malloc(cnt * sizeof(st)); ncur = 0;
    for (size_t i = 0; i < cap; i++) if (used[i]) cur[ncur++] = tab[i];
    free(tab); free(used);
  }
  size_t done = 0;
  for (size_t i = 0; i < ncur; i++) {
    if ((long)(i % nch) != ch) continue;
    bv a, b; memset(&a, 0, sizeof a); memset(&b, 0, sizeof b); a.w[0] = cur[i].a; b.w[0] = cur[i].b;
    dfs(d0, &a, &b); done++;
  }
  printf("a=%d d0=%d states=%zu chunk %d/%d (%zu states) nodes=%lld deepest surviving depth=%d => all die by depth %d\n",
         A, d0, ncur, ch, nch, done, nodes, deepest, deepest + 1);
  return 0;
}
