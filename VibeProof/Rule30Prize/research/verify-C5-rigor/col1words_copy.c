// Print all distinct column-1 words of length L for right half driven by periodic w from phase ph0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int L = atoi(argv[1]); const char *w = argv[2]; int ph0 = atoi(argv[3]);
    int p = strlen(w);
    int Wd = L + 1;
    uint64_t NC = 1ULL << Wd;
    uint8_t *seen = calloc(1ULL << L, 1);
    for (uint64_t x = 0; x < NC; x++) {
        uint64_t row = x; int Wc = Wd; uint64_t word = 0;
        for (int t = 0; t < L; t++) {
            word |= (row & 1ULL) << t;
            int d = w[(ph0 + t) % p] - '0';
            uint64_t mask = (1ULL << Wc) - 1;
            uint64_t left = ((row << 1) | (uint64_t)d) & mask;
            row = (left ^ (row | (row >> 1))) & mask;
        }
        seen[word] = 1;
    }
    for (uint64_t i = 0; i < (1ULL << L); i++) if (seen[i]) {
        for (int t = 0; t < L; t++) putchar(((i >> t) & 1) ? '1' : '0');
        putchar('\n');
    }
    return 0;
}
