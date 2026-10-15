// Rule 30 from every finite seed of width W (seed bits at positions 0..W-1, leftmost bit set),
// run N steps; for columns p in [-PAD, W-1+PAD] test whether the column is eventually periodic
// (period <= N/4, periodic on [N/2, N)). Report seeds with an eventually periodic column.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int W = atoi(argv[1]), N = atoi(argv[2]), PAD = atoi(argv[3]);
    int L = 2 * N + W + 4, off = N + 2;   // array index = off + position
    uint8_t *a = malloc(L), *b = malloc(L);
    int ncols = W + 2 * PAD;
    uint8_t *col = malloc((size_t)ncols * N);
    long found = 0;
    for (long seed = (1L << (W - 1)); seed < (1L << W); seed++) {
        if (!(seed & 1)) continue;          // rightmost bit set too (avoid translates / smaller widths)
        memset(a, 0, L);
        for (int i = 0; i < W; i++) a[off + i] = (seed >> (W - 1 - i)) & 1;
        for (int t = 0; t < N; t++) {
            for (int c = 0; c < ncols; c++) col[(size_t)c * N + t] = a[off - PAD + c];
            int lo = off - t - 2, hi = off + W + t + 2;
            if (lo < 1) lo = 1; if (hi > L - 2) hi = L - 2;
            for (int i = lo; i <= hi; i++) b[i] = a[i - 1] ^ (a[i] | a[i + 1]);
            b[lo - 1] = 0; b[hi + 1] = 0;
            uint8_t *tmp = a; a = b; b = tmp;
        }
        for (int c = 0; c < ncols; c++) {
            uint8_t *s = col + (size_t)c * N;
            for (int P = 1; P <= N / 4; P++) {
                int ok = 1;
                for (int t = N / 2; t + P < N; t++) if (s[t] != s[t + P]) { ok = 0; break; }
                if (ok) { printf("seed %ld (width %d): column %d eventually periodic, period %d\n", seed, W, c - PAD, P); found++; break; }
            }
        }
    }
    printf("W=%d N=%d done, periodic columns found: %ld\n", W, N, found);
    return 0;
}
