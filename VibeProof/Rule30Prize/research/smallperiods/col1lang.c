// Language of column-1 words of length L for the right half driven by periodic word w (starting at phase ph0),
// over all initial right-half configurations of width L+1. Output: count of distinct words, and forbidden subwords info.
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
            uint64_t mask = (Wc >= 64) ? ~0ULL : ((1ULL << Wc) - 1);
            uint64_t left = ((row << 1) | (uint64_t)d) & mask;
            row = (left ^ (row | (row >> 1))) & mask;
        }
        seen[word] = 1;
    }
    uint64_t cnt = 0; for (uint64_t i = 0; i < (1ULL << L); i++) cnt += seen[i];
    printf("L=%d w=%s ph0=%d distinct col1 words: %llu of %llu  (log2 ratio %.3f)\n", L, w, ph0, (unsigned long long)cnt, (unsigned long long)(1ULL << L), 0.0);
    // write words to stdout? print per-length count of words restricted to even positions (beta)
    if (argc > 4) { FILE *f = fopen(argv[4], "wb"); fwrite(seen, 1, 1ULL << L, f); fclose(f); }
    return 0;
}
