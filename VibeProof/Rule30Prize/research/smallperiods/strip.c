// Strip [1..W] of the right half, driven at column 0 by periodic word w (period p), adversarial input at column W+1.
// Trap orbit: Q phases, each a k-bit pattern for columns 1..k (bit i <-> column i+1).
// S0 = states whose columns 1..k equal orbit[(ph + sh) % Q] for some allowed shift sh (multiple of p).
// S = greatest subset of S0 closed under all inputs.  A = states from which the adversary can avoid S forever.
// usage: strip W w Q k orbit_ph0 ... orbit_ph{Q-1}   (orbit strings: char i = column i+1)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int W, p, Q, k;
const char *w;
uint64_t N, mask;
static inline uint64_t step(uint64_t s, int ph, int x) {
    int d = w[ph % p] - '0';
    uint64_t left = ((s << 1) | (uint64_t)d) & mask;
    uint64_t right = (s >> 1) | ((uint64_t)x << (W - 1));
    return (left ^ (s | right)) & mask;
}
int main(int argc, char **argv) {
    W = atoi(argv[1]); w = argv[2]; p = strlen(w); Q = atoi(argv[3]); k = atoi(argv[4]);
    uint64_t orb[64];
    for (int ph = 0; ph < Q; ph++) {
        const char *o = argv[5 + ph]; orb[ph] = 0;
        for (int i = 0; i < k; i++) if (o[i] == '1') orb[ph] |= 1ULL << i;
    }
    N = 1ULL << W; mask = N - 1;
    uint64_t kmask = (k == 64) ? ~0ULL : ((1ULL << k) - 1);
    uint8_t *S = calloc(Q * N, 1);
    for (int ph = 0; ph < Q; ph++) for (uint64_t s = 0; s < N; s++) {
        for (int sh = 0; sh < Q; sh += p) if ((s & kmask) == orb[(ph + sh) % Q]) { S[ph * N + s] = 1; break; }
    }
    int changed = 1, it = 0;
    while (changed) {
        changed = 0; it++;
        for (int ph = 0; ph < Q; ph++) { int nph = (ph + 1) % Q;
            for (uint64_t s = 0; s < N; s++) if (S[ph*N+s]) {
                if (!S[nph*N + step(s, ph, 0)] || !S[nph*N + step(s, ph, 1)]) { S[ph*N+s] = 0; changed = 1; }
            } }
    }
    uint64_t cs = 0; for (uint64_t i = 0; i < Q*N; i++) cs += S[i];
    printf("W=%d closed safe states: %llu (iters %d)\n", W, (unsigned long long)cs, it);
    if (cs == 0) return 0;
    // A: avoid set. start with complement of S, remove states all of whose successors are outside A.
    uint8_t *A = malloc(Q * N);
    for (uint64_t i = 0; i < Q*N; i++) A[i] = !S[i];
    changed = 1; it = 0;
    while (changed) {
        changed = 0; it++;
        for (int ph = 0; ph < Q; ph++) { int nph = (ph + 1) % Q;
            for (uint64_t s = 0; s < N; s++) if (A[ph*N+s]) {
                if (!A[nph*N + step(s, ph, 0)] && !A[nph*N + step(s, ph, 1)]) { A[ph*N+s] = 0; changed = 1; }
            } }
    }
    uint64_t ca = 0; for (uint64_t i = 0; i < Q*N; i++) ca += A[i];
    printf("adversary-avoid states: %llu of %llu (iters %d)\n", (unsigned long long)ca, (unsigned long long)(Q*N), it);
    // print a few phase counts
    for (int ph = 0; ph < Q; ph++) { uint64_t c = 0; for (uint64_t s = 0; s < N; s++) c += A[ph*N+s]; printf(" ph %d avoid %llu\n", ph, (unsigned long long)c); }
    return 0;
}
