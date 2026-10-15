// Independent re-implementation (verifier) of the adversarial right-strip certificate.
// Encoding deliberately different from reach3.c: column i (1..W) <-> bit (W - i), i.e. column 1 is the MSB.
// Successor computed by an explicit per-column loop and tabulated.
// Usage:
//   vreach W p maxit            -> all primitive necklaces of length p (canonical = lexicographically least rotation)
//   vreach W p maxit word...    -> only the given words (any rotation allowed; run as given)
// Output per word: word, stabilization time t* (first t with R_t == R_{t-p}), certified?, col-1 pattern per phase
// (0/1 determined, * free), sizes of stable sets per phase.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int W;
static uint32_t NS;
static uint32_t *tab[2][2]; // tab[d][x][s]

static int colv(uint32_t s, int i) { return (s >> (W - i)) & 1; } // column i of state s
static uint32_t succ(uint32_t s, int d, int x) {
    uint32_t r = 0;
    for (int i = 1; i <= W; i++) {
        int L = (i == 1) ? d : colv(s, i - 1);
        int C = colv(s, i);
        int R = (i == W) ? x : colv(s, i + 1);
        int v = L ^ (C | R);
        r |= (uint32_t)v << (W - i);
    }
    return r;
}

static void runword(const char *w, long maxit) {
    int p = (int)strlen(w);
    unsigned char *R = malloc(NS), *S = malloc(NS);
    unsigned char **hist = calloc(p, sizeof(unsigned char *));
    for (int i = 0; i < p; i++) hist[i] = NULL;
    memset(R, 1, NS);
    long t = 0; int stab = 1;
    while (1) {
        int ph = (int)(t % p);
        if (hist[ph] && memcmp(hist[ph], R, NS) == 0) break;
        if (!hist[ph]) hist[ph] = malloc(NS);
        memcpy(hist[ph], R, NS);
        if (t >= maxit) { stab = 0; break; }
        int d = w[ph] - '0';
        memset(S, 0, NS);
        for (uint32_t s = 0; s < NS; s++) if (R[s]) { S[tab[d][0][s]] = 1; S[tab[d][1][s]] = 1; }
        unsigned char *tmp = R; R = S; S = tmp; t++;
    }
    // stable sets: hist[ph] for all phases
    char pat[256]; int cert = 1;
    long sizes[256];
    for (int ph = 0; ph < p; ph++) {
        int seen0 = 0, seen1 = 0; long cnt = 0;
        for (uint32_t s = 0; s < NS; s++) if (hist[ph][s]) { cnt++; if (colv(s, 1)) seen1 = 1; else seen0 = 1; }
        sizes[ph] = cnt;
        pat[ph] = (seen0 && seen1) ? '*' : (seen1 ? '1' : '0');
        if (w[ph] == '0' && seen0 && seen1) cert = 0;
    }
    pat[p] = 0;
    printf("%s W=%d stab=%ld%s cert=%s col1=%s sizes=", w, W, t, stab ? "" : "(NOSTAB)", cert ? "YES" : "no", pat);
    for (int ph = 0; ph < p; ph++) printf("%ld%s", sizes[ph], ph + 1 < p ? "," : "\n");
    for (int i = 0; i < p; i++) free(hist[i]);
    free(hist); free(R); free(S);
}

int main(int argc, char **argv) {
    W = atoi(argv[1]); int p = atoi(argv[2]); long maxit = atol(argv[3]);
    NS = 1u << W;
    for (int d = 0; d < 2; d++) for (int x = 0; x < 2; x++) {
        tab[d][x] = malloc(sizeof(uint32_t) * NS);
        for (uint32_t s = 0; s < NS; s++) tab[d][x][s] = succ(s, d, x);
    }
    if (argc > 4) { for (int a = 4; a < argc; a++) runword(argv[a], maxit); return 0; }
    // enumerate primitive necklaces of length p: string-based minimal rotation check
    char w[64], r[64];
    long count = 0, certc = 0;
    for (uint64_t x = 0; x < (1ULL << p); x++) {
        for (int i = 0; i < p; i++) w[i] = '0' + ((x >> i) & 1); // LSB-first, different from reach3
        w[p] = 0;
        int canon = 1, prim = 1;
        for (int k = 1; k < p; k++) {
            for (int i = 0; i < p; i++) r[i] = w[(i + k) % p];
            r[p] = 0;
            int c = strcmp(r, w);
            if (c < 0) canon = 0;
            if (c == 0) prim = 0;
        }
        if (!canon || !prim) continue;
        count++;
        runword(w, maxit);
    }
    fprintf(stderr, "p=%d necklaces=%ld\n", p, count);
    return 0;
}
