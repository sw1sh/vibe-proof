// Left half driven by periodic word w at column 0, from a random finite config of width W0 (edge at -W0).
// Record left diagonals: D_j(t) = cell(t, -W0 - t + j). For each j, estimate transient (time after which periodic with period dividing 2^k up to maxP).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int W0 = atoi(argv[2]); int steps = atoi(argv[3]); unsigned seed = atoi(argv[4]); int J = atoi(argv[5]);
    int p = strlen(w);
    int N = W0 + steps + 4;
    uint8_t *x = calloc(N, 1), *y = calloc(N, 1);   // index i <-> position -(i+1)
    srand(seed);
    for (int i = 0; i < W0 - 1; i++) x[i] = rand() & 1;
    x[W0 - 1] = 1;
    // diag[j][t]
    uint8_t *diag = calloc((size_t)J * steps, 1);
    for (int t = 0; t < steps; t++) {
        int edge = W0 + t; // edge position -(W0+t) <-> index W0+t-1
        for (int j = 0; j < J; j++) {
            int pos = -(W0 + t) + j; // position
            if (pos <= -1) diag[(size_t)j * steps + t] = x[-pos - 1]; else diag[(size_t)j * steps + t] = 2; // 2 = right of column -1
        }
        int ct = w[t % p] - '0';
        int lim = W0 + t + 1;
        for (int i = 0; i <= lim && i < N - 1; i++) {
            uint8_t right = (i == 0) ? ct : x[i - 1];
            y[i] = x[i + 1] ^ (x[i] | right);
        }
        uint8_t *tmp = x; x = y; y = tmp;
    }
    // for each j: find smallest period P (power of 2 up to 4096) and transient Tj over times where the diag is defined (pos<=-1)
    for (int j = 0; j < J; j += (j < 64 ? 1 : 16)) {
        uint8_t *d = diag + (size_t)j * steps;
        int tmax = steps; // defined while pos <= -1: -(W0+t)+j <= -1 -> t >= j - W0 + 1 ... all t if j < W0
        int bestP = -1, bestT = -1;
        for (int P = 1; P <= 4096 && P < steps / 3; P *= 2) {
            int T = tmax - P;
            while (T > 0 && d[T - 1] != 2 && d[T - 1 + P] != 2 && d[T - 1] == d[T - 1 + P]) T--;
            if (T < tmax - 2 * P - 50) { bestP = P; bestT = T; break; }
        }
        // position at time bestT
        if (bestP > 0) printf("j=%d period %d transient %d (pos at transient: %d)\n", j, bestP, bestT, -(W0 + bestT) + j);
        else printf("j=%d not periodic within window\n", j);
    }
    return 0;
}
