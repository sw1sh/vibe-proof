// Verifier's independent C implementation of the adversarial right-strip certificate.
// Encoding: column j (1..W) at bit (W-j): column 1 is the MSB, column W is bit 0.
// Necklaces enumerated as strings: w is canonical iff w <= every rotation (strcmp) and w is primitive
// (no proper rotation equals w).
// Usage: cert W p [word]   -> prints, for each canonical primitive word of length p (or just `word`):
//   word stab=<t> zdet=<0|1> pat=<col-1 value per phase, * = both>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int W; static uint32_t N, MASK, MSB; static size_t NW;

static inline uint32_t stepf(uint32_t s, uint32_t d, uint32_t x) {
    uint32_t left = (s >> 1) | (d ? MSB : 0);
    uint32_t right = ((s << 1) & MASK) | x;
    return (left ^ (s | right)) & MASK;
}

static void run(const char *w, int p) {
    uint64_t *R = calloc(NW, 8), *S = calloc(NW, 8);
    uint64_t **hist = calloc(p, sizeof(uint64_t *));
    for (uint32_t s = 0; s < N; s++) R[s >> 6] |= 1ULL << (s & 63);
    long t = 0;
    for (;;) {
        int ph = (int)(t % p);
        if (hist[ph] && memcmp(hist[ph], R, NW * 8) == 0) break;
        if (!hist[ph]) hist[ph] = malloc(NW * 8);
        memcpy(hist[ph], R, NW * 8);
        if (t > 1000000) { printf("%s NOSTAB\n", w); return; }
        uint32_t d = (uint32_t)(w[ph] - '0');
        memset(S, 0, NW * 8);
        for (uint32_t s = 0; s < N; s++) {
            if (!((R[s >> 6] >> (s & 63)) & 1)) continue;
            uint32_t a = stepf(s, d, 0), b = stepf(s, d, 1);
            S[a >> 6] |= 1ULL << (a & 63);
            S[b >> 6] |= 1ULL << (b & 63);
        }
        uint64_t *tmp = R; R = S; S = tmp; t++;
    }
    char pat[64]; int zdet = 1;
    for (int ph = 0; ph < p; ph++) {
        int seen0 = 0, seen1 = 0;
        for (uint32_t s = 0; s < N; s++) if ((hist[ph][s >> 6] >> (s & 63)) & 1) { if (s & MSB) seen1 = 1; else seen0 = 1; }
        pat[ph] = (seen0 && seen1) ? '*' : (seen1 ? '1' : '0');
        if (w[ph] == '0' && seen0 && seen1) zdet = 0;
        if (!seen0 && !seen1) { pat[ph] = 'E'; } // empty set (should never happen)
    }
    pat[p] = 0;
    printf("%s stab=%ld zdet=%d pat=%s\n", w, t, zdet, pat);
    for (int ph = 0; ph < p; ph++) free(hist[ph]);
    free(hist); free(R); free(S);
}

int main(int argc, char **argv) {
    W = atoi(argv[1]); int p = atoi(argv[2]);
    N = 1u << W; MASK = N - 1; MSB = 1u << (W - 1); NW = (N + 63) / 64;
    if (argc > 3) { run(argv[3], (int)strlen(argv[3])); return 0; }
    char w[64], r[64];
    for (uint64_t x = 0; x < (1ULL << p); x++) {
        for (int i = 0; i < p; i++) w[i] = (char)('0' + ((x >> i) & 1)); // any bijection is fine
        w[p] = 0;
        int canon = 1, prim = 1;
        for (int k = 1; k < p; k++) {
            for (int i = 0; i < p; i++) r[i] = w[(i + k) % p];
            r[p] = 0;
            int c = strcmp(r, w);
            if (c < 0) canon = 0;
            if (c == 0) prim = 0;
        }
        if (canon && prim) run(w, p);
    }
    return 0;
}
