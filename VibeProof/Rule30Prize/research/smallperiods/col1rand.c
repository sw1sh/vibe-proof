// For a given driver word (string of length L), count distinct column-1 words of length L over all initial configs of width L+1.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *dw = argv[1]; int L = strlen(dw);
    int Wd = L + 1;
    uint64_t NC = 1ULL << Wd;
    uint8_t *seen = calloc(1ULL << L, 1);
    for (uint64_t x = 0; x < NC; x++) {
        uint64_t row = x; uint64_t word = 0; uint64_t mask = (1ULL << Wd) - 1;
        for (int t = 0; t < L; t++) {
            word |= (row & 1ULL) << t;
            uint64_t d = dw[t] - '0';
            uint64_t left = ((row << 1) | d) & mask;
            row = (left ^ (row | (row >> 1))) & mask;
        }
        seen[word] = 1;
    }
    uint64_t cnt = 0; for (uint64_t i = 0; i < (1ULL << L); i++) cnt += seen[i];
    printf("%s : %llu\n", dw, (unsigned long long)cnt);
    return 0;
}
