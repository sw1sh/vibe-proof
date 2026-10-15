// Arbitrary-input automaton test for the w-driven right half of rule 30.
// Strip = columns 1..k, driver column 0 = w[phase], input column k+1 = arbitrary bit u.
// State = (phase, s) with s in {0,1}^k (bit j-1 = column j). Output = column 1 = bit 0.
// Test: every nontrivial SCC has output constant on each class of its cyclic period decomposition.
// If PASS: for every right-half configuration (even infinite), column 1 is eventually periodic.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P, K; static int wb[64]; static uint32_t MASK;
static inline uint32_t succ(uint32_t id, int u) {
    uint32_t phi = id >> K, s = id & MASK;
    uint32_t left = ((s << 1) | wb[phi]) & MASK;
    uint32_t right = (s >> 1) | ((uint32_t)u << (K - 1));
    uint32_t ns = (left ^ (s | right)) & MASK;
    uint32_t nphi = (phi + 1) % P;
    return (nphi << K) | ns;
}
static long gcdl(long a, long b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { long t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
    const char *w = argv[1]; K = atoi(argv[2]); int verbose = argc > 3 ? atoi(argv[3]) : 0;
    P = strlen(w); for (int i = 0; i < P; i++) wb[i] = w[i] - '0';
    MASK = (K == 32) ? 0xffffffffu : ((1u << K) - 1);
    uint32_t N = (uint32_t)P << K;
    int32_t *index = malloc(sizeof(int32_t) * N), *low = malloc(sizeof(int32_t) * N);
    uint32_t *stack = malloc(sizeof(uint32_t) * N), *cstack = malloc(sizeof(uint32_t) * N);
    uint8_t *onstack = calloc(N, 1), *it = calloc(N, 1);
    int32_t *comp = malloc(sizeof(int32_t) * N);
    for (uint32_t i = 0; i < N; i++) { index[i] = -1; comp[i] = -1; }
    int32_t idx = 0, ncomp = 0; uint32_t sp = 0, csp = 0;
    // iterative Tarjan
    for (uint32_t r = 0; r < N; r++) {
        if (index[r] >= 0) continue;
        cstack[csp++] = r; index[r] = low[r] = idx++; stack[sp++] = r; onstack[r] = 1; it[r] = 0;
        while (csp) {
            uint32_t v = cstack[csp - 1];
            if (it[v] < 2) {
                uint32_t wv = succ(v, it[v]); it[v]++;
                if (index[wv] < 0) {
                    index[wv] = low[wv] = idx++; stack[sp++] = wv; onstack[wv] = 1; it[wv] = 0; cstack[csp++] = wv;
                } else if (onstack[wv]) { if (index[wv] < low[v]) low[v] = index[wv]; }
            } else {
                if (low[v] == index[v]) {
                    uint32_t x;
                    do { x = stack[--sp]; onstack[x] = 0; comp[x] = ncomp; } while (x != v);
                    ncomp++;
                }
                csp--;
                if (csp) { uint32_t p = cstack[csp - 1]; if (low[v] < low[p]) low[p] = low[v]; }
            }
        }
    }
    free(index); free(low); free(onstack); free(it); free(cstack);
    // for each component: BFS levels; gcd; check outputs per class
    int64_t *lvl = malloc(sizeof(int64_t) * N); for (uint32_t i = 0; i < N; i++) lvl[i] = INT64_MIN;
    uint32_t *queue = stack; // reuse
    int fail = 0; long nontriv = 0; long maxsize = 0;
    int8_t *done = calloc(ncomp, 1);
    for (uint32_t r = 0; r < N && !fail; r++) {
        int c = comp[r]; if (done[c]) continue; done[c] = 1;
        // BFS from r within component
        uint32_t qh = 0, qt = 0; queue[qt++] = r; lvl[r] = 0; long g = 0; long size = 0; int selfloop = 0;
        while (qh < qt) {
            uint32_t v = queue[qh++]; size++;
            for (int u = 0; u < 2; u++) {
                uint32_t x = succ(v, u);
                if (comp[x] != c) continue;
                if (x == v) selfloop = 1;
                if (lvl[x] == INT64_MIN) { lvl[x] = lvl[v] + 1; queue[qt++] = x; }
                else g = gcdl(g, lvl[v] + 1 - lvl[x]);
            }
        }
        if (size == 1 && !selfloop) continue;
        nontriv++; if (size > maxsize) maxsize = size;
        if (g == 0) { fprintf(stderr, "g=0?\n"); g = 1; }
        // check output per class
        int8_t *cls = malloc(g); memset(cls, -1, g);
        for (uint32_t i = 0; i < qt; i++) {
            uint32_t v = queue[i]; long cl = ((lvl[v] % g) + g) % g; int o = (v & MASK) & 1;
            if (cls[cl] < 0) cls[cl] = o; else if (cls[cl] != o) { fail = 1; if (verbose) {
                printf("  FAIL comp size %ld period %ld at state phase=%u s=", size, g, v >> K);
                for (int j = 0; j < K; j++) putchar(((v >> j) & 1) ? '1' : '0'); printf("\n"); }
                break; }
        }
        if (!fail && verbose) {
            printf("  comp size %ld period %ld output: ", size, g);
            for (long i = 0; i < g && i < 200; i++) putchar('0' + cls[i]); printf("\n");
        }
        free(cls);
    }
    printf("%s k=%d %s (nontrivial SCCs checked: %ld, max size %ld)\n", w, K, fail ? "FAIL" : "PASS", nontriv, maxsize);
    return 0;
}
