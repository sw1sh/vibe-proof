// Growth rate of the number of paths in the strip relaxation (i) in the whole graph, (ii) inside the
// complement of SAFE (paths that never enter the maximal trap), via power iteration on path counts.
// usage: entropy w b safefile iters
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
static int P, b; static const char *W;
static inline int succ(int phi, uint32_t s, uint32_t out[2]) {
    uint64_t full = (uint64_t)(W[phi] - '0') | ((uint64_t)s << 1);
    uint64_t nw = (full ^ ((full >> 1) | (full >> 2))) & ((1ULL << b) - 1);
    // column b's new value depends on the free input when column b is white
    if ((s >> (b - 1)) & 1) { out[0] = (uint32_t)nw; return 1; } // OR already 1: input irrelevant
    out[0] = (uint32_t)nw; out[1] = (uint32_t)(nw ^ (1u << (b - 1))); return 2;
}
int main(int argc, char **argv) {
    W = argv[1]; P = strlen(W); b = atoi(argv[2]); int iters = atoi(argv[4]);
    uint32_t N = (uint32_t)P << b, M = 1u << b;
    uint8_t *safe = malloc(N); FILE *f = fopen(argv[3], "rb"); if (fread(safe, 1, N, f) != N) return 1; fclose(f);
    double *v = malloc(sizeof(double) * N), *u = malloc(sizeof(double) * N);
    for (int mode = 0; mode < 2; mode++) {
        for (uint32_t i = 0; i < N; i++) v[i] = (mode == 1 && safe[i]) ? 0.0 : 1.0;
        double lam = 0, logsum = 0; int cnt = 0;
        for (int it = 0; it < iters; it++) {
            double tot = 0;
            for (uint32_t id = 0; id < N; id++) {
                if (mode == 1 && safe[id]) { u[id] = 0; continue; }
                int phi = id >> b; uint32_t s = id & (M - 1), o[2]; int k = succ(phi, s, o); double acc = 0;
                for (int i = 0; i < k; i++) { uint32_t n2 = ((uint32_t)((phi + 1) % P) << b) | o[i]; acc += v[n2]; }
                u[id] = acc; tot += acc;
            }
            double prev = 0; for (uint32_t id = 0; id < N; id++) prev += v[id];
            lam = tot / prev; if (it >= iters - 4 * P) { logsum += log(lam); cnt++; }
            for (uint32_t id = 0; id < N; id++) v[id] = u[id] / tot * N;
        }
        printf("w=%s b=%d %s growth rate per step %.5f (log2 %.4f)\n", W, b, mode ? "trap-avoiding" : "all paths   ", exp(logsum / cnt), logsum / cnt / log(2.0));
    }
    return 0;
}
