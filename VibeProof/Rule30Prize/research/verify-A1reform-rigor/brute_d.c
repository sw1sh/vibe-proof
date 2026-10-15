// Brute-force check of claim (d): count rows L of width <= W (bits L(1..W), L(k)=0 for k>W)
// whose ZBL forward evolution has x_1(t) = 1 for every even t <= W-1.  Expect 2^floor(W/2).
// Also report how many of them additionally satisfy the constraint at t = W (if W even) for information.
// Packed row r: bit (k-1) = L(k).  ZBL step: Z(L)(k) = L(k+1) ^ (L(k) | L(k-1)), L(0) = 0.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static inline uint64_t zstep(uint64_t r) { return (r >> 1) ^ (r | (r << 1)); }
int main(int argc, char **argv) {
  int W1 = atoi(argv[1]);
  for (int W = 0; W <= W1; W++) {
    uint64_t n = (uint64_t)1 << W, cnt = 0, cntW = 0;
    for (uint64_t r0 = 0; r0 < n; r0++) {
      uint64_t r = r0; int good = 1;
      for (int t = 0; t <= W - 1; t++) {
        if ((t & 1) == 0 && !(r & 1)) { good = 0; break; }
        r = zstep(r);
      }
      if (good) {
        cnt++;
        // r is now row at time W (if W>=1); constraint at t=W when W even
        if (W % 2 == 0) { if (W == 0 ? (r0 & 1) : (r & 1)) cntW++; } else cntW++;
      }
    }
    printf("W=%2d count=%llu expected=%llu %s   (also satisfying t=W constraint: %llu)\n", W,
           (unsigned long long)cnt, (unsigned long long)((uint64_t)1 << (W / 2)),
           cnt == ((uint64_t)1 << (W / 2)) ? "OK" : "MISMATCH", (unsigned long long)cntW);
    fflush(stdout);
  }
  return 0;
}
