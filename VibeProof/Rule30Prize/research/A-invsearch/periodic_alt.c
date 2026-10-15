// Search spatially periodic rule-30 configurations (ring of size q) lying on temporal cycles in which some column
// alternates 0,1,0,1,... exactly.  Report the first examples.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q; static uint32_t M;
static inline uint32_t rotl(uint32_t x, int k){ return ((x << k) | (x >> (q - k))) & M; }
static inline uint32_t rotr(uint32_t x, int k){ return ((x >> k) | (x << (q - k))) & M; }
// bit i = cell i; left neighbour of i is i-1 -> (x << 1) brings bit i-1 to i
static inline uint32_t r30(uint32_t x){ return rotl(x,1) ^ (x | rotr(x,1)); }
int main(int argc, char **argv){
  int q0 = atoi(argv[1]), q1 = atoi(argv[2]);
  for (q = q0; q <= q1; q++){
    M = (q == 32) ? 0xffffffffu : ((1u << q) - 1);
    uint8_t *seen = calloc((size_t)1 << q, 1);
    int found = 0; long cycles = 0;
    for (uint32_t s = 0; s <= M && !found; s++){
      if (seen[s]) continue;
      // follow trajectory, marking with 2 = on current path
      uint32_t x = s; 
      while (!seen[x]) { seen[x] = 2; x = r30(x); }
      if (seen[x] == 2) {
        // x is on a new cycle
        cycles++;
        uint32_t c = x; int tau = 0; uint32_t y = c;
        do { y = r30(y); tau++; } while (y != c);
        if (tau % 2 == 0){
          // check each column j: values at times 0..tau-1 alternate
          for (int j = 0; j < q && !found; j++){
            int b0 = (c >> j) & 1, ok = 1; y = c;
            for (int t = 0; t < tau; t++){ if (((y >> j) & 1) != ((b0 + t) & 1)) { ok = 0; break; } y = r30(y); }
            if (ok){ found = 1; printf("q=%d: cycle period %d, column %d alternates; config ", q, tau, j);
              for (int i = 0; i < q; i++) putchar(((c >> i) & 1) ? '1' : '0'); printf("\n"); }
          }
        }
      }
      // mark path as done
      x = s; while (seen[x] == 2) { seen[x] = 1; x = r30(x); }
    }
    if (!found) printf("q=%d: no cycle with an alternating column (%ld cycles)\n", q, cycles);
    fflush(stdout);
    free(seen);
  }
  return 0;
}
