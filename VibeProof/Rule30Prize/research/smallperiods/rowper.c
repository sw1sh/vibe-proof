// Right half driven by periodic w from random finite config of width W0. For rows (right diagonals) j born at column 0
// at time j (Row_j(t) = cell(t, t-j), t >= j), compute the least period of Row_j over t in [j, steps) (power of 2 test up to 2^20).
// Store the full space-time (bits) for t < steps, positions < steps + W0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int W0 = atoi(argv[2]); int steps = atoi(argv[3]); unsigned seed = atoi(argv[4]); int jstep = atoi(argv[5]);
    int p = strlen(w);
    int N = W0 + steps + 4;
    uint8_t *grid = calloc((size_t)steps * N, 1);
    uint8_t *x = calloc(N + 2, 1), *y = calloc(N + 2, 1);
    srand(seed);
    for (int i = 1; i < W0; i++) x[i] = rand() & 1;
    x[W0] = 1;
    for (int t = 0; t < steps; t++) {
        x[0] = w[t % p] - '0';
        memcpy(grid + (size_t)t * N, x, N);
        for (int i = 1; i < N; i++) y[i] = x[i-1] ^ (x[i] | x[i+1]);
        uint8_t *tmp = x; x = y; y = tmp;
    }
    for (int j = 0; j < steps / 2; j += jstep) {
        // sequence s(t) = grid[t][t-j] for t in [j, steps)
        int len = steps - j;
        int best = -1;
        for (int P = 1; P <= len / 2; P *= 2) {
            int ok = 1;
            for (int t = j; t + P < steps; t++) if (grid[(size_t)t * N + (t - j)] != grid[(size_t)(t + P) * N + (t + P - j)]) { ok = 0; break; }
            if (ok) { best = P; break; }
        }
        // also eventual period with transient: check from t >= j + len/2
        int beste = -1;
        for (int P = 1; P <= len / 4; P *= 2) {
            int ok = 1;
            for (int t = j + len / 2; t + P < steps; t++) if (grid[(size_t)t * N + (t - j)] != grid[(size_t)(t + P) * N + (t + P - j)]) { ok = 0; break; }
            if (ok) { beste = P; break; }
        }
        printf("j=%d c(j)=%c purePeriod=%d eventualPeriod(2nd half)=%d\n", j, w[j % p], best, beste);
    }
    return 0;
}
