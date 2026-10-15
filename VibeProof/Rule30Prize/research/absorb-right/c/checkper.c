// Check: for word w (start phase ph), random configs of width W: is column 1 periodic with period P
// on [T0, N)?  Reports the number of failures and the maximal "last violation" time.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static u64 rng_s;
static u64 rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static void step(u64 *r, int n, int c) {
    u64 carry = (u64)c;
    for (int j = 0; j < n; j++) { u64 cur = r[j], nxt = (j + 1 < n) ? r[j + 1] : 0;
        u64 left = (cur << 1) | carry, right = (cur >> 1) | (nxt << 63); carry = cur >> 63; r[j] = left ^ (cur | right); }
}
int main(int argc, char **argv) {
    const char *w = argv[1]; long T0 = atol(argv[2]); long N = atol(argv[3]); int trials = atoi(argv[4]); long W = atol(argv[5]);
    int P = strlen(w); int wb[512]; for (int i = 0; i < P; i++) wb[i] = w[i] - '0';
    int nw = (int)((W + N + 128) / 64 + 2);
    u64 *row = malloc(nw * 8); uint8_t *col = malloc(N);
    int fails = 0; long maxlast = -1;
    for (int tr = 0; tr < trials; tr++) {
        rng_s = (u64)(tr + 1) * 0x9E3779B97F4A7C15ULL ^ 0x123456789ULL; for (int i = 0; i < 5; i++) rnd();
        memset(row, 0, nw * 8);
        long Wt = (tr % 4 == 0) ? 0 : (tr % 4 == 1 ? 7 : (tr % 4 == 2 ? W / 10 : W));
        for (long i = 0; i < Wt; i++) if (rnd() & 1) row[i / 64] |= 1ULL << (i % 64);
        int ph = tr % P;
        for (long t = 0; t < N; t++) { col[t] = row[0] & 1; long need = (N - t) + 2; int nwa = (int)(need / 64 + 2); if (nwa > nw) nwa = nw; step(row, nwa, wb[(ph + t) % P]); }
        long last = -1; for (long t = 0; t + P < N; t++) if (col[t] != col[t + P]) last = t;
        if (last >= T0 + P) fails++;   // allow phase offset < P
        if (last > maxlast) maxlast = last;
    }
    printf("%s P=%d: trials=%d fails(after T0=%ld)=%d max last violation=%ld\n", w, P, trials, T0, fails, maxlast);
    return 0;
}
