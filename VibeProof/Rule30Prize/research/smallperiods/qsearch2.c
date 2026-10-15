// Left half driven by periodic word cprime (effective boundary c'), from finite configs of width W (leftmost 1 at -W).
// Constraint pattern: string pat over {0,1,*} of the same period: a(t) must equal pat[t mod p] unless '*'.
// Report the best survival time and histogram.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int W = atoi(argv[1]); const char *cp = argv[2]; const char *pat = argv[3]; long maxT = atol(argv[4]);
    int p = strlen(cp);
    long len = W + maxT + 4;
    uint8_t *x = malloc(len), *y = malloc(len);
    long best = -1; uint64_t bestX = 0; long hist[64] = {0};
    for (uint64_t X = (1ULL << (W-1)); X < (1ULL << W); X++) {
        memset(x, 0, len); memset(y, 0, len);
        for (int i = 0; i < W; i++) x[i] = (X >> i) & 1;
        long t; long lim = W + 1;
        for (t = 0; t < maxT; t++) {
            char want = pat[t % p];
            if (want != '*' && x[0] != (want - '0')) break;
            int ct = cp[t % p] - '0';
            for (long i = 0; i <= lim; i++) { uint8_t right = (i == 0) ? ct : x[i-1]; y[i] = x[i+1] ^ (x[i] | right); }
            lim++;
            uint8_t *tmp = x; x = y; y = tmp;
        }
        if (t > best) { best = t; bestX = X; }
        int b = 0; long s = t; while (s > 1) { s >>= 1; b++; } hist[b]++;
    }
    printf("W=%d c'=%s pat=%s best survival %ld (X=%llx) hist:", W, cp, pat, best, (unsigned long long)bestX);
    for (int b = 0; b < 30; b++) if (hist[b]) printf(" %d:%ld", b, hist[b]);
    printf("\n");
    return 0;
}
