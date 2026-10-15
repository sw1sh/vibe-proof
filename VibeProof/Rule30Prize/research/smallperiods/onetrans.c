#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int p = strlen(w); int k = atoi(argv[2]), Q = atoi(argv[3]); const char *cfg = argv[4]; int steps = atoi(argv[5]);
    int W0 = strlen(cfg); int N = W0 + steps + 4;
    uint8_t *a = calloc(N + 2, 1), *b = calloc(N + 2, 1);
    for (int i = 0; i < W0; i++) a[i + 1] = cfg[i] - '0';
    uint32_t *hist = malloc(steps * 4); long wid = W0;
    for (int t = 0; t < steps; t++) {
        a[0] = w[t % p] - '0';
        uint32_t s = 0; for (int i = 1; i <= k; i++) s |= (uint32_t)a[i] << (i - 1);
        hist[t] = s; wid++;
        for (long i = 1; i <= wid && i < N; i++) b[i] = a[i-1] ^ (a[i] | a[i+1]);
        uint8_t *tmp = a; a = b; b = tmp;
    }
    long T = steps - Q; while (T > 0 && hist[T-1] == hist[T-1+Q]) T--;
    // also list times of 'kicks': t where hist[t] != hist[t+Q], last 20
    printf("transient %ld; mismatch times (last 30):", T);
    int cnt = 0; for (long t = steps - Q - 1; t >= 0 && cnt < 30; t--) if (hist[t] != hist[t+Q]) { printf(" %ld", t); cnt++; }
    printf("\n");
    return 0;
}
