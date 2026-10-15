// as rightwin but print the start of the final p-periodic tail for p = 5 and the global longest windows over time
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXW 1048576
static uint64_t row[MAXW / 64 + 2], nrow[MAXW / 64 + 2];
int main(int argc, char **argv) {
    int T = atoi(argv[1]); unsigned seed = atoi(argv[2]); int w0 = atoi(argv[3]); int P = atoi(argv[4]);
    srand(seed);
    int words = (w0 + T + 2 + 63) / 64 + 1;
    memset(row, 0, sizeof row);
    for (int i = 0; i < w0; i++) if (rand() & 1) row[i >> 6] |= 1ULL << (i & 63);
    row[(w0 - 1) >> 6] |= 1ULL << ((w0 - 1) & 63);
    int phase = 1;
    unsigned char *g = malloc(T);
    int ng = 0;
    for (int t = 0; t < T; t++) {
        int c0 = (phase + t) & 1;
        if (c0 == 0) g[ng++] = row[0] & 1;
        int lim = (w0 + (T - t) + 2 + 63) / 64 + 1; if (lim > words) lim = words;
        for (int k = 0; k < lim; k++) {
            uint64_t cur = row[k];
            uint64_t left = (cur << 1) | (k == 0 ? (uint64_t)c0 : (row[k - 1] >> 63));
            uint64_t right = (cur >> 1) | ((k + 1 < words ? row[k + 1] : 0) << 63);
            nrow[k] = left ^ (cur | right);
        }
        memcpy(row, nrow, lim * 8);
    }
    // find start of final P-periodic tail
    int i = ng - 1 - P;
    while (i >= 0 && g[i + P] == g[i]) i--;
    printf("seed %u: final %d-periodic tail starts at k=%d of %d (tail length %d)\n", seed, P, i + 1, ng, ng - (i + 1));
    printf("last 60: ");
    for (int k = ng - 60; k < ng; k++) putchar('0' + g[k]);
    printf("\n");
    return 0;
}
