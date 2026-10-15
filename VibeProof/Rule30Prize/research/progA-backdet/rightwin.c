// Right half p>=1 driven by c(t) alternating (c(0)=phase). Record column 1 at white times (c(t)=0).
// Then find maximal p-periodic windows of that sequence for p in [1, PMAX].
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXW 262144
static uint64_t row[MAXW / 64 + 2], nrow[MAXW / 64 + 2];
int main(int argc, char **argv) {
    int T = atoi(argv[1]); unsigned seed = atoi(argv[2]); int w0 = atoi(argv[3]); int PMAX = atoi(argv[4]);
    srand(seed);
    int words = (w0 + T + 2 + 63) / 64 + 1;
    if (words > MAXW / 64) { fprintf(stderr, "too big\n"); return 1; }
    memset(row, 0, sizeof row);
    for (int i = 0; i < w0; i++) if (rand() & 1) row[i >> 6] |= 1ULL << (i & 63);
    row[(w0 - 1) >> 6] |= 1ULL << ((w0 - 1) & 63);
    // bit i <-> position p = i+1
    int phase = 1; // c(0) = 1 (black first)
    unsigned char *g = malloc(T);
    int ng = 0;
    for (int t = 0; t < T; t++) {
        int c0 = (phase + t) & 1;
        if (c0 == 0) g[ng++] = row[0] & 1;
        // new(p) = old(p-1) ^ (old(p) | old(p+1)); old(0) = c0
        for (int k = 0; k < words; k++) {
            uint64_t cur = row[k];
            uint64_t left = (cur << 1) | (k == 0 ? (uint64_t)c0 : (row[k - 1] >> 63));
            uint64_t right = (cur >> 1) | ((k + 1 < words ? row[k + 1] : 0) << 63);
            nrow[k] = left ^ (cur | right);
        }
        memcpy(row, nrow, words * 8);
    }
    // maximal periodic windows: for each p, scan runs where g[i+p]==g[i]
    // report for each p the window [k0, k0+len] with largest (len - k0) and the longest window overall after k>=ng/2
    for (int p = 1; p <= PMAX; p++) {
        int bestlen = 0, bestk0 = 0; double bestratio = -1e9; int rk0 = 0, rlen = 0;
        int i = 0;
        while (i + p < ng) {
            if (g[i + p] != g[i]) { i++; continue; }
            int j = i;
            while (j + p < ng && g[j + p] == g[j]) j++;
            int len = (j - i) + p; // window [i, i+len) is p-periodic
            if (len > bestlen) { bestlen = len; bestk0 = i; }
            if (len - i > bestratio) { bestratio = len - i; rk0 = i; rlen = len; }
            i = j + 1;
        }
        if (bestlen > 3 * p) printf("p=%d longest window len=%d at k0=%d ; max(len-k0)=%d (k0=%d,len=%d)\n", p, bestlen, bestk0, (int)bestratio, rk0, rlen);
    }
    printf("ng=%d\n", ng);
    return 0;
}
