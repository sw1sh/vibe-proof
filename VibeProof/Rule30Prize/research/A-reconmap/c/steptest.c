/* read y as a 0/1 string from stdin lines, output L(1..n) using the multi-limb step */
#include <stdio.h>
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
int main(void) {
  char line[1000];
  while (fgets(line, sizeof line, stdin)) {
    int n = strlen(line); while (n && (line[n-1] == '\n' || line[n-1] == '\r')) n--;
    bv a, b, c; memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
    for (int k = 0; k < n; k++) { step(&a, &b, k, line[k] - '0', &c); putchar('0' + (int)(c.w[0] & 1)); a = b; b = c; }
    putchar('\n');
  }
  return 0;
}
