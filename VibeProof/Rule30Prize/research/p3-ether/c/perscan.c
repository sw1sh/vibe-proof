// For every right half x with support in [1,n] (all 2^n) and every driver phase, run the right half driven by
// w^inf for S steps (light-cone truncated, exact for column 1) and test whether column 1 at the white times of
// the driver is eventually periodic: smallest period p <= PMAX (in white samples) holding on the last half.
// Prints a histogram of (period in steps) and onset statistics.  usage: perscan w n S PMAX
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static const char *W; static int P;
#define MAXWD 2048
static uint64_t row[MAXWD], nw[MAXWD];
static void step(int nwords, int c) {
    // row bit i of word j = column 64*j + i + 1 ; left neighbor of column 1 is c
    uint64_t carry = (uint64_t)c;
    for (int j = 0; j < nwords; j++) {
        uint64_t x = row[j], left = (x << 1) | carry, right = (x >> 1) | (j + 1 < nwords ? row[j + 1] << 63 : 0);
        carry = x >> 63; nw[j] = left ^ (x | right);
    }
    memcpy(row, nw, 8 * nwords);
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); int n = atoi(argv[2]); int S = atoi(argv[3]); int PMAX = atoi(argv[4]);
    int nwhite = 0; for (int i = 0; i < P; i++) if (W[i] == '0') nwhite++;
    uint8_t *seq = malloc(S + 1);
    long hist[64] = {0}; long nper = 0, nnot = 0, total = 0; long maxonset = 0; long persum[5000] = {0};
    for (long x = 0; x < (1L << n); x++) for (int ph = 0; ph < P; ph++) {
        int nwords = (S + n + 2) / 64 + 2; if (nwords > MAXWD) { fprintf(stderr, "too wide\n"); return 1; }
        memset(row, 0, 8 * nwords); row[0] = (uint64_t)x;
        int L = 0;
        for (int t = 0; t < S; t++) {
            int c = W[(ph + t) % P] - '0';
            if (!c) seq[L++] = (uint8_t)(row[0] & 1);
            // light cone: after step t, only columns up to S - t + 1 matter
            int need = (S - t + 2) / 64 + 2; if (need < nwords) { nwords = need; }
            step(nwords, c);
        }
        total++;
        int found = 0;
        for (int p = 1; p <= PMAX && !found && 4 * p <= L / 2; p++) {
            int ok = 1; for (int i = L / 2; i + p < L; i++) if (seq[i] != seq[i + p]) { ok = 0; break; }
            if (ok) { found = p; }
        }
        if (found) { nper++; int onset = L - found; while (onset > 0 && seq[onset - 1] == seq[onset - 1 + found]) onset--;
            long steps = (long)found * P / nwhite; if (steps < 5000) persum[steps]++; long onsteps = (long)onset * P / nwhite; if (onsteps > maxonset) maxonset = onsteps; }
        else nnot++;
    }
    printf("w=%s n=%d S=%d: runs %ld, column-1-at-white eventually periodic (p<=%d samples, checked on last half) %ld, not %ld; max onset ~%ld steps\n",
           W, n, S, total, PMAX, nper, nnot, maxonset);
    printf("  periods (in steps):"); for (int s = 0; s < 5000; s++) if (persum[s]) printf(" %d:%ld", s, persum[s]); printf("\n");
    return 0;
}
