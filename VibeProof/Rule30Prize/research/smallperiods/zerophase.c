// For driver w (periodic, phase 0 at t=0), over all right-half configs of width L+1, compute for each time t < L
// the set of possible values of b(t) = column 1 (bitmask: 1 = value 0 possible, 2 = value 1 possible).
// Report, for zero-phases of w (c(t) = 0), the last time t at which both values are possible, and the forced pattern after.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int L = atoi(argv[2]);
    int p = strlen(w);
    int Wd = L + 1;
    uint64_t NC = 1ULL << Wd;
    uint64_t mask = (1ULL << Wd) - 1;
    uint64_t seen0 = 0, seen1 = 0; // bit t set if b(t)=0 / b(t)=1 occurs
    for (uint64_t x = 0; x < NC; x++) {
        uint64_t row = x, word = 0;
        for (int t = 0; t < L; t++) {
            word |= (row & 1ULL) << t;
            uint64_t d = w[t % p] - '0';
            uint64_t left = ((row << 1) | d) & mask;
            row = (left ^ (row | (row >> 1))) & mask;
        }
        seen1 |= word; seen0 |= ~word;
    }
    printf("%s L=%d: ", w, L);
    int lastfree = -1;
    for (int t = 0; t < L; t++) {
        int c = w[t % p] - '0';
        int s = ((seen0 >> t) & 1) | (((seen1 >> t) & 1) << 1);
        char ch = s == 3 ? '*' : (s == 1 ? '0' : '1');
        if (c == 0 && s == 3) lastfree = t;
        putchar(c == 0 ? ch : (s == 3 ? '+' : (s == 1 ? 'o' : 'i')));
    }
    printf("   last free zero-phase time: %d\n", lastfree);
    return 0;
}
