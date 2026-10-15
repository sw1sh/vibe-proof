// Independent re-derivation of the adversarial right-strip certificate (claim C4).
// Layout (deliberately different from reach*.c): column i (1..W) of the right half is bit (W - i),
// so column 1 is the MOST significant bit and column W is bit 0.
// Two independent ways of computing the limit sets L_phi:
//   (A) forward iteration R_0 = all, R_{k+1} = Post_{w[k mod p]}(R_k), stop when R_t == R_{t-p};
//   (B) Kahn in-degree pruning on the phase-layered graph (nodes (phi,s), edges to (phi+1, step(s,w[phi],x))):
//       the nodes never pruned are exactly those with infinite backward paths = lim R_{phi+mp}.
// Usage:
//   cert selftest W TMAX            -- check the explicit step table against a direct rule-30 run
//   cert dump W                     -- print the successor table (for the Python cross-check)
//   cert word W w [maxit]           -- analyse one word
//   cert len W p [maxit]            -- analyse every primitive necklace (min rotation) of length p
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int W;
static uint32_t NS;
static uint32_t *SUCC; // SUCC[(2*d + x) * NS + s]

static int getcol(uint32_t s, int i) { return (int)((s >> (W - i)) & 1u); }

static uint32_t step_explicit(uint32_t s, int d, int x) {
    uint32_t out = 0;
    for (int i = 1; i <= W; i++) {
        int left = (i == 1) ? d : getcol(s, i - 1);
        int ctr = getcol(s, i);
        int right = (i == W) ? x : getcol(s, i + 1);
        int nv = left ^ (ctr | right); // rule 30: left xor (center or right)
        out |= (uint32_t)nv << (W - i);
    }
    return out;
}

static void build_table(void) {
    NS = 1u << W;
    SUCC = malloc((size_t)4 * NS * sizeof(uint32_t));
    for (int d = 0; d < 2; d++)
        for (int x = 0; x < 2; x++)
            for (uint32_t s = 0; s < NS; s++) SUCC[(size_t)(2 * d + x) * NS + s] = step_explicit(s, d, x);
}

static int selftest(int tmax) {
    // direct rule 30 from a single black cell, positions -tmax-2 .. tmax+W+3
    int off = tmax + 2, width = 2 * tmax + W + 8;
    uint8_t *a = calloc(width, 1), *b = calloc(width, 1);
    a[off] = 1;
    int bad = 0;
    const int known[20] = {1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1};
    for (int t = 0; t < tmax; t++) {
        if (t < 20 && a[off] != known[t]) { printf("center mismatch at t=%d\n", t); bad++; }
        for (int q = 1; q < width - 1; q++) b[q] = a[q - 1] ^ (a[q] | a[q + 1]);
        b[0] = 0; b[width - 1] = 0;
        // strip state at t and t+1
        uint32_t s0 = 0, s1 = 0;
        for (int i = 1; i <= W; i++) { s0 |= (uint32_t)a[off + i] << (W - i); s1 |= (uint32_t)b[off + i] << (W - i); }
        uint32_t pred = SUCC[(size_t)(2 * a[off] + a[off + W + 1]) * NS + s0];
        if (pred != s1) { printf("strip step mismatch at t=%d\n", t); bad++; }
        // column -1 identity: cell(t,-1) = c(t+1) xor (c(t) or cell(t,1))
        if (a[off - 1] != (b[off] ^ (a[off] | a[off + 1]))) { printf("col -1 identity fails at t=%d\n", t); bad++; }
        uint8_t *tmp = a; a = b; b = tmp;
    }
    printf("selftest W=%d tmax=%d: %s\n", W, tmax, bad ? "FAIL" : "ok");
    free(a); free(b);
    return bad;
}

// Analyse one word. Returns certified flag. Prints a line.
static int analyse(const char *w, long maxit) {
    int p = (int)strlen(w);
    // (A) forward iteration with byte sets
    uint8_t **hist = calloc(p, sizeof(uint8_t *));
    uint8_t *R = malloc(NS), *S = malloc(NS);
    memset(R, 1, NS);
    long t = 0; int stab_ok = 1;
    for (;;) {
        int ph = (int)(t % p);
        if (hist[ph] && memcmp(hist[ph], R, NS) == 0) break;
        if (!hist[ph]) hist[ph] = malloc(NS);
        memcpy(hist[ph], R, NS);
        if (t > maxit) { stab_ok = 0; break; }
        int d = w[ph] - '0';
        memset(S, 0, NS);
        const uint32_t *T0 = SUCC + (size_t)(2 * d) * NS, *T1 = SUCC + (size_t)(2 * d + 1) * NS;
        for (uint32_t s = 0; s < NS; s++) if (R[s]) { S[T0[s]] = 1; S[T1[s]] = 1; }
        uint8_t *tmp = R; R = S; S = tmp;
        t++;
    }
    // (B) Kahn pruning on the layered graph
    size_t NN = (size_t)p * NS;
    uint32_t *indeg = calloc(NN, sizeof(uint32_t));
    uint8_t *removed = calloc(NN, 1);
    uint32_t *queue = malloc(NN * sizeof(uint32_t));
    for (int ph = 0; ph < p; ph++) {
        int d = w[ph] - '0'; int nph = (ph + 1) % p;
        for (uint32_t s = 0; s < NS; s++)
            for (int x = 0; x < 2; x++) indeg[(size_t)nph * NS + SUCC[(size_t)(2 * d + x) * NS + s]]++;
    }
    size_t qh = 0, qt = 0;
    for (size_t v = 0; v < NN; v++) if (indeg[v] == 0) { removed[v] = 1; queue[qt++] = (uint32_t)v; }
    while (qh < qt) {
        size_t v = queue[qh++];
        int ph = (int)(v / NS); uint32_t s = (uint32_t)(v % NS);
        int d = w[ph] - '0'; int nph = (ph + 1) % p;
        for (int x = 0; x < 2; x++) {
            size_t u = (size_t)nph * NS + SUCC[(size_t)(2 * d + x) * NS + s];
            if (--indeg[u] == 0) { removed[u] = 1; queue[qt++] = (uint32_t)u; }
        }
    }
    // compare (A) and (B), and compute column-1 status per phase from (B)
    int agree = 1;
    char statA[65], statB[65];
    int certified = 1;
    for (int ph = 0; ph < p; ph++) {
        int seenA[2] = {0, 0}, seenB[2] = {0, 0};
        for (uint32_t s = 0; s < NS; s++) {
            int inA = hist[ph][s] ? 1 : 0;
            int inB = removed[(size_t)ph * NS + s] ? 0 : 1;
            if (inA != inB) agree = 0;
            int c1 = getcol(s, 1);
            if (inA) seenA[c1] = 1;
            if (inB) seenB[c1] = 1;
        }
        statA[ph] = (seenA[0] && seenA[1]) ? '*' : seenA[1] ? '1' : seenA[0] ? '0' : 'E';
        statB[ph] = (seenB[0] && seenB[1]) ? '*' : seenB[1] ? '1' : seenB[0] ? '0' : 'E';
        if (w[ph] == '0' && statB[ph] != '0' && statB[ph] != '1') certified = 0;
    }
    statA[p] = statB[p] = 0;
    if (!stab_ok) certified = 0;
    printf("%s W=%d stab=%ld%s colA=%s colB=%s A==B:%s %s\n", w, W, t, stab_ok ? "" : "(NOSTAB)", statA, statB,
           agree ? "yes" : "NO", certified ? "CERTIFIED" : "-");
    for (int ph = 0; ph < p; ph++) free(hist[ph]);
    free(hist); free(R); free(S); free(indeg); free(removed); free(queue);
    return certified;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage\n"); return 2; }
    W = atoi(argv[2]);
    build_table();
    if (!strcmp(argv[1], "selftest")) return selftest(atoi(argv[3]));
    if (!strcmp(argv[1], "dump")) {
        for (int d = 0; d < 2; d++) for (int x = 0; x < 2; x++) for (uint32_t s = 0; s < NS; s++)
            printf("%d %d %u %u\n", d, x, s, SUCC[(size_t)(2 * d + x) * NS + s]);
        return 0;
    }
    if (!strcmp(argv[1], "word")) { long maxit = argc > 4 ? atol(argv[4]) : 100000; analyse(argv[3], maxit); return 0; }
    if (!strcmp(argv[1], "len")) {
        int p = atoi(argv[3]); long maxit = argc > 4 ? atol(argv[4]) : 100000;
        int ncert = 0, nwords = 0;
        char w[65], r[65];
        for (uint64_t x = 0; x < (1ull << p); x++) {
            for (int i = 0; i < p; i++) w[i] = (char)('0' + ((x >> (p - 1 - i)) & 1));
            w[p] = 0;
            // keep w iff it is primitive and lexicographically strictly smaller than all its proper rotations
            int keep = 1;
            for (int k = 1; k < p && keep; k++) {
                for (int i = 0; i < p; i++) r[i] = w[(i + k) % p];
                r[p] = 0;
                if (strcmp(r, w) <= 0) keep = 0; // equal => not primitive; smaller => not minimal
            }
            if (!keep) continue;
            nwords++;
            ncert += analyse(w, maxit);
        }
        printf("SUMMARY W=%d p=%d necklaces=%d certified=%d\n", W, p, nwords, ncert);
    }
    return 0;
}
