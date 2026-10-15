// For driver word w (periodic), phase ph0, compute number of distinct column-1 words of length L for L = Lmin..Lmax
// over all initial configs of width L+1. Uses incremental approach: just recompute per L.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint64_t count(int L, const char *w, int ph0) {
    int p = strlen(w);
    int Wd = L + 1;
    uint64_t NC = 1ULL << Wd;
    uint64_t nw = 1ULL << L;
    uint64_t *seen = calloc((nw + 63) / 64, 8);
    uint64_t mask = (1ULL << Wd) - 1;
    for (uint64_t x = 0; x < NC; x++) {
        uint64_t row = x, word = 0;
        for (int t = 0; t < L; t++) {
            word |= (row & 1ULL) << t;
            uint64_t d = w[(ph0 + t) % p] - '0';
            uint64_t left = ((row << 1) | d) & mask;
            row = (left ^ (row | (row >> 1))) & mask;
        }
        seen[word >> 6] |= 1ULL << (word & 63);
    }
    uint64_t c = 0;
    for (uint64_t i = 0; i < (nw + 63) / 64; i++) c += __builtin_popcountll(seen[i]);
    free(seen);
    return c;
}
int main(int argc, char **argv) {
    const char *w = argv[1]; int Lmin = atoi(argv[2]), Lmax = atoi(argv[3]);
    printf("%s:", w);
    for (int L = Lmin; L <= Lmax; L += 2) { printf(" %llu", (unsigned long long)count(L, w, 0)); fflush(stdout); }
    printf("\n");
    return 0;
}
