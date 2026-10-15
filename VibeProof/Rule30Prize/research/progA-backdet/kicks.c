#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXW 2097152
static uint64_t row[MAXW / 64 + 2], nrow[MAXW / 64 + 2];
int main(int argc, char **argv) {
    int T = atoi(argv[1]); unsigned seed = atoi(argv[2]); int w0 = atoi(argv[3]); int B = atoi(argv[4]);
    srand(seed);
    int words = (w0 + T + 2 + 63) / 64 + 1;
    memset(row, 0, sizeof row);
    for (int i = 0; i < w0; i++) if (rand() & 1) row[i >> 6] |= 1ULL << (i & 63);
    row[(w0 - 1) >> 6] |= 1ULL << ((w0 - 1) & 63);
    unsigned char *g = malloc(T);
    int ng = 0;
    for (int t = 0; t < T; t++) {
        int c0 = (1 + t) & 1;
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
    printf("seed %u kicks (g[k+5]!=g[k]) per block of %d:", seed, B);
    for (int b = 0; b + B <= ng - 5; b += B) {
        int c = 0;
        for (int k = b; k < b + B; k++) c += (g[k + 5] != g[k]);
        printf(" %d", c);
    }
    printf("\n");
    return 0;
}
