/* Zero-tail search for the period-2 reconstruction map (Q_01).
   ZBL u-coordinates: u_t(k) = cell(T+t,-k); column y_t = u_t(1); y_{2s} = 1, y_{2s+1} = f_s free.
   Anti-diagonals D_k[j] = u_j(k-j), j = 0..k-1.  D_{k+1}[k] = y_k,
   D_{k+1}[j] = D_{k+1}[j+1] ^ (D_k[j] | D_{k-1}[j]).  L(k) = D_k[0].
   For a given a: is there any f with L(k) = 0 for all k in [a, B]?  Report the least B where none survives.
   Phase 1: BFS with exact dedup of (D_{k-1}, D_k) up to depth d0 (no constraint, d0 < a).
   Phase 2: DFS from each phase-1 state with the constraint L(k) = 0 for k >= a.
   Usage: zt a d0 maxdepth
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NW 4
typedef struct { uint64_t w[NW]; } bv;
static inline uint64_t sxor64(uint64_t s) { s ^= s >> 1; s ^= s >> 2; s ^= s >> 4; s ^= s >> 8; s ^= s >> 16; s ^= s >> 32; return s; }
/* compute D_{k+1} from D_{k-1}, D_k, y_k */
static inline void step(const bv *Dkm1, const bv *Dk, int k, int yk, bv *out) {
  bv g;
  for (int i = 0; i < NW; i++) g.w[i] = Dk->w[i] | Dkm1->w[i];
  /* mask bits >= k */
  for (int i = 0; i < NW; i++) {
    int lo = 64 * i;
    if (k <= lo) g.w[i] = 0;
    else if (k < lo + 64) g.w[i] &= (k - lo == 64) ? ~0ULL : ((1ULL << (k - lo)) - 1);
  }
  int carry = 0;
  for (int i = NW - 1; i >= 0; i--) {
    uint64_t s = sxor64(g.w[i]);
    if (carry) s = ~s;
    carry ^= __builtin_parityll(g.w[i]);
    out->w[i] = s;
  }
  /* now out[j] = xor_{i>=j} g[i] for all j (bits >= k give 0 or 1 depending on carry; mask them) */
  for (int i = 0; i < NW; i++) {
    int lo = 64 * i;
    uint64_t m;
    if (k <= lo) m = 0; else if (k >= lo + 64) m = ~0ULL; else m = (1ULL << (k - lo)) - 1;
    uint64_t v = out->w[i] & m;
    if (yk) v ^= m;
    out->w[i] = v;
  }
  if (yk) out->w[k >> 6] |= 1ULL << (k & 63);
}
/* ---------- hash set of state pairs ---------- */
typedef struct { bv a, b; } st;
static st *tab; static uint8_t *used; static size_t cap, cnt;
static uint64_t hsh(const st *s) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < NW; i++) { h ^= s->a.w[i]; h *= 1099511628211ULL; h ^= s->b.w[i]; h *= 1099511628211ULL; } return h ^ (h >> 29); }
static void hinit(size_t c) { cap = c; cnt = 0; tab = calloc(cap, sizeof(st)); used = calloc(cap, 1); if (!tab || !used) { fprintf(stderr, "oom\n"); exit(1); } }
static void hfree(void) { free(tab); free(used); }
static void hput(const st *s) {
  size_t i = hsh(s) & (cap - 1);
  while (used[i]) { if (!memcmp(&tab[i], s, sizeof(st))) return; i = (i + 1) & (cap - 1); }
  used[i] = 1; tab[i] = *s; cnt++;
  if (cnt * 2 > cap) { fprintf(stderr, "hash full\n"); exit(1); }
}
static int A, MAXD;
static long long surv[512];
static int deepest = 0;
static long long nodes = 0;
static void dfs(int k, const bv *Dkm1, const bv *Dk) {
  /* D_k computed (depth k). compute D_{k+1} */
  if (k >= MAXD) { fprintf(stderr, "MAXD reached\n"); exit(2); }
  int ys[2], ny;
  if (k % 2 == 0) { ys[0] = 1; ny = 1; } else { ys[0] = 0; ys[1] = 1; ny = 2; }
  for (int q = 0; q < ny; q++) {
    bv Dn; step(Dkm1, Dk, k, ys[q], &Dn); nodes++;
    int Lk1 = Dn.w[0] & 1;
    if (k + 1 >= A && Lk1) continue;
    surv[k + 1]++;
    if (k + 1 > deepest) deepest = k + 1;
    dfs(k + 1, Dk, &Dn);
  }
}
int main(int argc, char **argv) {
  A = atoi(argv[1]); int d0 = atoi(argv[2]); MAXD = argc > 3 ? atoi(argv[3]) : 250;
  if (MAXD > 64 * NW - 2) MAXD = 64 * NW - 2;
  if (d0 >= A) d0 = A - 1;
  /* BFS phase */
  size_t c = 1 << 10; st *cur = malloc(sizeof(st)); size_t ncur = 1; memset(cur, 0, sizeof(st));
  for (int k = 0; k < d0; k++) {
    while (c < 4 * ncur + 16) c <<= 1;
    hinit(c);
    for (size_t i = 0; i < ncur; i++) {
      int ys[2], ny;
      if (k % 2 == 0) { ys[0] = 1; ny = 1; } else { ys[0] = 0; ys[1] = 1; ny = 2; }
      for (int q = 0; q < ny; q++) {
        st s; s.a = cur[i].b; step(&cur[i].a, &cur[i].b, k, ys[q], &s.b);
        hput(&s);
      }
    }
    free(cur); cur = malloc(cnt * sizeof(st)); ncur = 0;
    for (size_t i = 0; i < cap; i++) if (used[i]) cur[ncur++] = tab[i];
    hfree();
  }
  fprintf(stderr, "a=%d: %zu distinct states at depth %d\n", A, ncur, d0);
  for (size_t i = 0; i < ncur; i++) dfs(d0, &cur[i].a, &cur[i].b);
  printf("a=%d d0=%d states=%zu nodes=%lld  first dead depth B(a)=%d\n", A, d0, ncur, nodes, deepest + 1);
  printf("survivors by depth from a:");
  for (int k = A; k <= deepest; k++) printf(" %lld", surv[k]);
  printf("\n");
  return 0;
}
