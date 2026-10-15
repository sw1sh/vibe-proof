// Adversarial strip reachable-set; for each word, report which columns k (1..W) are determined at all phases
// in the stabilized set, and whether column 1 is determined at all zero-phases.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int W; static uint64_t N, mask; static size_t words;
int main(int argc, char **argv) {
    W = atoi(argv[1]); int p = atoi(argv[2]); long maxit = atol(argv[3]); const char *only = argc > 4 ? argv[4] : NULL;
    N = 1ULL << W; mask = N - 1; words = (N + 63) / 64;
    char w[64];
    for (uint64_t x = 0; x < (1ULL << p); x++) {
        int canon = 1, prim = 1;
        for (int r = 1; r < p; r++) { uint64_t y = ((x >> r) | (x << (p - r))) & ((1ULL << p) - 1); if (y < x) canon = 0; if (y == x) prim = 0; }
        if (!canon || !prim) continue;
        for (int i = 0; i < p; i++) w[i] = '0' + ((x >> (p - 1 - i)) & 1);
        w[p] = 0;
        if (only && strcmp(only, w)) continue;
        uint64_t *R = malloc(words * 8), *S = malloc(words * 8);
        uint64_t **hist = calloc(p, sizeof(uint64_t*));
        memset(R, 0xff, words * 8); if (N % 64) R[words-1] &= (1ULL << (N % 64)) - 1;
        long t = 0; int ok = 1;
        for (;;) {
            int ph = t % p;
            if (hist[ph] && memcmp(hist[ph], R, words * 8) == 0) break;
            if (!hist[ph]) hist[ph] = malloc(words * 8);
            memcpy(hist[ph], R, words * 8);
            if (t > maxit) { ok = 0; break; }
            uint64_t d = w[ph] - '0';
            memset(S, 0, words * 8);
            for (size_t k = 0; k < words; k++) { uint64_t m = R[k]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; uint64_t s = ((uint64_t)k << 6) | b;
                uint64_t left = ((s << 1) | d) & mask;
                uint64_t n0 = (left ^ (s | (s >> 1))) & mask, n1 = (left ^ (s | ((s >> 1) | (1ULL << (W - 1))))) & mask;
                S[n0 >> 6] |= 1ULL << (n0 & 63); S[n1 >> 6] |= 1ULL << (n1 & 63); } }
            uint64_t *tmp = R; R = S; S = tmp; t++;
        }
        // per column, per phase: OR and AND over states
        uint64_t orv[64] = {0}, andv[64]; for (int ph = 0; ph < p; ph++) andv[ph] = mask;
        for (int ph = 0; ph < p; ph++) { uint64_t *H = hist[ph];
            for (uint64_t s = 0; s < N; s++) if ((H[s >> 6] >> (s & 63)) & 1) { orv[ph] |= s; andv[ph] &= s; } }
        printf("%s stab=%ld%s cols determined at all phases:", w, t, ok ? "" : "(NOSTAB)");
        for (int k = 0; k < W; k++) { int all = 1; for (int ph = 0; ph < p; ph++) if (((orv[ph] >> k) & 1) != ((andv[ph] >> k) & 1)) all = 0; if (all) printf(" %d", k + 1); }
        int zdet = 1; for (int ph = 0; ph < p; ph++) if (w[ph] == '0' && ((orv[ph] & 1) != (andv[ph] & 1))) zdet = 0;
        printf("  | col1 at zero-phases %s\n", zdet ? "DETERMINED" : "free");
        for (int ph = 0; ph < p; ph++) free(hist[ph]); free(hist); free(R); free(S);
    }
    return 0;
}
