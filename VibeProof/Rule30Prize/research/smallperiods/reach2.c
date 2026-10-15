// Like reach.c but loops over all words of length p (given), canonical rotation, primitive; reports words where
// column 1 is determined at every zero-phase in the stabilized reachable set (=> c cannot be eventually w-periodic).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int W; static uint64_t N, mask; static size_t words;
static int analyze(const char *w, int p, long maxit, long *stab, int *det) {
    uint64_t *R = malloc(words * 8), *S = malloc(words * 8);
    uint64_t **hist = calloc(p, sizeof(uint64_t*));
    memset(R, 0xff, words * 8);
    if (N % 64) R[words-1] &= (1ULL << (N % 64)) - 1;
    long t = 0; int ok = 1;
    for (;;) {
        int ph = t % p;
        if (hist[ph] && memcmp(hist[ph], R, words * 8) == 0) break;
        if (!hist[ph]) hist[ph] = malloc(words * 8);
        memcpy(hist[ph], R, words * 8);
        if (t > maxit) { ok = 0; break; }
        uint64_t d = w[ph] - '0';
        memset(S, 0, words * 8);
        for (size_t k = 0; k < words; k++) {
            uint64_t m = R[k];
            while (m) {
                int b = __builtin_ctzll(m); m &= m - 1;
                uint64_t s = ((uint64_t)k << 6) | b;
                uint64_t left = ((s << 1) | d) & mask;
                uint64_t n0 = (left ^ (s | (s >> 1))) & mask, n1 = (left ^ (s | ((s >> 1) | (1ULL << (W - 1))))) & mask;
                S[n0 >> 6] |= 1ULL << (n0 & 63); S[n1 >> 6] |= 1ULL << (n1 & 63);
            }
        }
        uint64_t *tmp = R; R = S; S = tmp;
        t++;
    }
    *stab = t;
    int alldet = 1;
    for (int ph = 0; ph < p; ph++) {
        det[ph] = -1;
        if (!hist[ph]) { alldet = 0; continue; }
        uint64_t *H = hist[ph]; uint64_t cnt = 0, c1 = 0;
        for (size_t k = 0; k < words; k++) { cnt += __builtin_popcountll(H[k]); c1 += __builtin_popcountll(H[k] & 0xAAAAAAAAAAAAAAAAULL); }
        det[ph] = (c1 == 0) ? 0 : (c1 == cnt ? 1 : 2);
        if (w[ph] == '0' && det[ph] == 2) alldet = 0;
    }
    for (int ph = 0; ph < p; ph++) free(hist[ph]);
    free(hist); free(R); free(S);
    return ok && alldet;
}
int main(int argc, char **argv) {
    W = atoi(argv[1]); int p = atoi(argv[2]); long maxit = atol(argv[3]);
    N = 1ULL << W; mask = N - 1; words = (N + 63) / 64;
    char w[64]; int det[64];
    for (uint64_t x = 0; x < (1ULL << p); x++) {
        // canonical: x minimal among rotations, primitive
        int canon = 1, prim = 1;
        for (int r = 1; r < p; r++) {
            uint64_t y = ((x >> r) | (x << (p - r))) & ((1ULL << p) - 1);
            if (y < x) canon = 0;
            if (y == x) prim = 0;
        }
        if (!canon || !prim) continue;
        for (int i = 0; i < p; i++) w[i] = '0' + ((x >> (p - 1 - i)) & 1);
        w[p] = 0;
        long stab;
        int res = analyze(w, p, maxit, &stab, det);
        printf("%s %s stab=%ld det=", w, res ? "EXCLUDED" : "-", stab);
        for (int i = 0; i < p; i++) putchar(det[i] == 0 ? '0' : det[i] == 1 ? '1' : det[i] == 2 ? '*' : '?');
        putchar('\n');
    }
    return 0;
}
