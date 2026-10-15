// Search finite left-half configurations X (support within [-W,-1]) such that, driven by alternating c
// (c(t) = (t + ph) % 2), the left column a = x_{-1} satisfies a(t) = !c(t+1) whenever c(t) = 1, for as long as possible.
// Enumerate via DFS on the time-0 row from position -1 leftwards using the transposed (left-permutive) structure:
// a(t) for c(t)=1 times is forced, which forces cells. Simpler: brute-force all 2^W configs for small W, simulate.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int W = atoi(argv[1]); int ph = atoi(argv[2]); long maxT = atol(argv[3]);
    // left half: cells at positions -1..-(W+maxT); index i <-> position -(i+1)
    long len = W + maxT + 4;
    uint8_t *x = malloc(len), *y = malloc(len);
    long best = -1; uint64_t bestX = 0; long hist[64] = {0};
    for (uint64_t X = 0; X < (1ULL << W); X++) {
        if (W > 0 && !((X >> (W-1)) & 1)) continue; // leftmost 1 exactly at -W
        memset(x, 0, len); memset(y, 0, len);
        for (int i = 0; i < W; i++) x[i] = (X >> i) & 1;
        long t; long lim = W + 1;
        for (t = 0; t < maxT; t++) {
            int ct = (t + ph) % 2, cn = (t + 1 + ph) % 2;
            if (ct == 1 && x[0] != !cn) break;
            // step: new(p) = old(p-1) xor (old(p) or old(p+1)); i <-> p=-(i+1): old(p-1) = x[i+1], old(p+1) = x[i-1] (x[-1] = c)
            for (long i = 0; i <= lim; i++) {
                uint8_t right = (i == 0) ? ct : x[i-1];
                y[i] = x[i+1] ^ (x[i] | right);
            }
            lim++;
            uint8_t *tmp = x; x = y; y = tmp;
        }
        long surv = t;
        if (surv > best) { best = surv; bestX = X; }
        int b = 0; long s = surv; while (s > 1) { s >>= 1; b++; } hist[b]++;
    }
    printf("W=%d ph=%d best survival %ld (X=%llx)  hist(log2):", W, ph, best, (unsigned long long)bestX);
    for (int b = 0; b < 20; b++) if (hist[b]) printf(" %d:%ld", b, hist[b]);
    printf("\n");
    return 0;
}
