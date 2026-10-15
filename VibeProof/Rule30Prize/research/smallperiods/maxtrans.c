// For driver w, find right-half configs (width W0) maximizing the time until column 1..k becomes periodic with period Q
// (measured as: last time t < steps-2Q where columns 1..k at t and t+Q differ, +1). Random restarts + bit-flip hill climbing.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static const char *w; static int p, k, Q, steps;
static long transient(const uint8_t *init, int W0) {
    int N = W0 + steps + 4;
    uint8_t *a = calloc(N + 2, 1), *b = calloc(N + 2, 1);
    memcpy(a + 1, init, W0);
    uint32_t *hist = malloc(steps * sizeof(uint32_t));
    long wid = W0;
    for (int t = 0; t < steps; t++) {
        a[0] = w[t % p] - '0';
        uint32_t s = 0; for (int i = 1; i <= k; i++) s |= (uint32_t)a[i] << (i - 1);
        hist[t] = s;
        wid++;
        for (long i = 1; i <= wid && i < N; i++) b[i] = a[i-1] ^ (a[i] | a[i+1]);
        uint8_t *tmp = a; a = b; b = tmp;
    }
    long T = steps - Q;
    while (T > 0 && hist[T - 1] == hist[T - 1 + Q]) T--;
    free(a); free(b); free(hist);
    return T;
}
int main(int argc, char **argv) {
    w = argv[1]; p = strlen(w); k = atoi(argv[2]); Q = atoi(argv[3]); int W0 = atoi(argv[4]); steps = atoi(argv[5]); int restarts = atoi(argv[6]); unsigned seed = atoi(argv[7]);
    srand(seed);
    uint8_t *x = malloc(W0), *best = malloc(W0);
    long gbest = -1;
    for (int r = 0; r < restarts; r++) {
        for (int i = 0; i < W0; i++) x[i] = rand() & 1;
        long cur = transient(x, W0);
        for (int it = 0; it < 400; it++) {
            int i = rand() % W0; x[i] ^= 1;
            long v = transient(x, W0);
            if (v >= cur) cur = v; else x[i] ^= 1;
        }
        if (cur > gbest) { gbest = cur; memcpy(best, x, W0); }
    }
    printf("w=%s k=%d Q=%d W0=%d steps=%d best transient %ld\n", w, k, Q, W0, steps, gbest);
    for (int i = 0; i < W0; i++) putchar('0' + best[i]); putchar('\n');
    return 0;
}
