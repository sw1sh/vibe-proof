// Verifier: direct ZBL simulation of S[1..m] . v . 0^inf (|v| <= 3), independent of the window reduction.
// bit k = depth k, bit 0 = wall. stripe(k) = k odd. Checks d <= m+5 and death time <= d-1+31.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int getb(const uint64_t *a, int k) { return (a[k >> 6] >> (k & 63)) & 1; }
static void setb(uint64_t *a, int k, int v) { if (v) a[k >> 6] |= 1ULL << (k & 63); else a[k >> 6] &= ~(1ULL << (k & 63)); }
int main(int argc, char **argv) {
  int M = argc > 1 ? atoi(argv[1]) : 1000;
  int maxsurv[2][8]; int argmax[2][8];
  memset(maxsurv, -1, sizeof maxsurv);
  int nbits = M + 3 + M + 200, nw = nbits / 64 + 2;
  uint64_t *a = malloc(nw * 8), *b = malloc(nw * 8);
  long bad = 0;
  for (int m = M - 12; m <= M; m++) for (int v = 0; v < 8; v++) {
    memset(a, 0, nw * 8);
    for (int k = 1; k <= m; k++) setb(a, k, k & 1);
    for (int i = 0; i < 3; i++) setb(a, m + 1 + i, (v >> i) & 1);
    int d = -1;
    for (int k = 1; k <= m + 10; k++) if (getb(a, k) != (k & 1)) { d = k; break; }
    if (d < 0 || d > m + 5) { printf("bad d m=%d v=%d d=%d\n", m, v, d); bad++; continue; }
    int death = -1;
    for (int t = 0; t <= m + 200; t++) {
      if (t % 2 == 0 && !getb(a, 1)) { death = t; break; }
      for (int i = 0; i < nw; i++) {
        uint64_t r1 = (a[i] >> 1) | (i + 1 < nw ? a[i + 1] << 63 : 0);
        uint64_t l1 = (a[i] << 1) | (i > 0 ? a[i - 1] >> 63 : 0);
        b[i] = r1 ^ (a[i] | l1);
      }
      b[0] &= ~1ULL;
      uint64_t *tmp = a; a = b; b = tmp;
    }
    if (death < 0) { printf("no death m=%d v=%d\n", m, v); bad++; continue; }
    int surv = death - (d - 1);
    if (surv > 31) { printf("VIOLATION m=%d v=%d d=%d death=%d\n", m, v, d, death); bad++; }
    if (surv > maxsurv[m & 1][v]) { maxsurv[m & 1][v] = surv; argmax[m & 1][v] = m; }
  }
  for (int q = 0; q < 2; q++) for (int v = 0; v < 8; v++)
    printf("m%%2=%d v=(b0,b1,b2)=(%d,%d,%d): max death-(d-1) over m<=%d is %d (at m=%d)\n", q, v & 1, (v >> 1) & 1, (v >> 2) & 1, M, maxsurv[q][v], argmax[q][v]);
  printf("violations/bad=%ld\n", bad);
  return 0;
}
