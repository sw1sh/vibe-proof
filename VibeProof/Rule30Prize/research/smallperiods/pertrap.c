// Right half driven by w from a spatially periodic initial configuration (pattern pat repeated, width huge).
// Report the trap transient (columns 1..k periodic with period Q at the end).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int k = atoi(argv[2]), Q = atoi(argv[3]); int steps = atoi(argv[4]); int maxlen = atoi(argv[5]);
    int p = strlen(w);
    int N = 2 * steps + 10;
    uint8_t *a = calloc(N + 2, 1), *b = calloc(N + 2, 1);
    uint32_t *hist = malloc(steps * 4);
    int found = 0;
    for (int len = 1; len <= maxlen; len++) for (uint32_t pat = 0; pat < (1u << len); pat++) {
        // primitive patterns only (skip if pat has smaller period) - not needed, fine
        for (int i = 1; i <= N; i++) a[i] = (pat >> ((i - 1) % len)) & 1;
        for (int t = 0; t < steps; t++) {
            a[0] = w[t % p] - '0';
            uint32_t s = 0; for (int i = 1; i <= k; i++) s |= (uint32_t)a[i] << (i - 1);
            hist[t] = s;
            for (int i = 1; i < N; i++) b[i] = a[i-1] ^ (a[i] | a[i+1]);
            b[N] = 0;
            uint8_t *tmp = a; a = b; b = tmp;
        }
        long T = steps - Q; while (T > 0 && hist[T-1] == hist[T-1+Q]) T--;
        if (T > steps - 4 * Q) { printf("len %d pat %x: NOT trapped within %d steps\n", len, pat, steps); found++; }
    }
    printf("done, %d untrapped\n", found);
    return 0;
}
