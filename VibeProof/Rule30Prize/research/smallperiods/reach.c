// Adversarial strip reachable-set iteration.
// Strip columns 1..W (bit i <-> column i+1), driver c(t) = w[t mod p], adversarial (free) input at column W+1.
// R_0 = all states. R_{t+1} = Post(R_t). Iterate until R_{t+p} == R_t (as sets at the same phase). Report for each phase
// whether column 1 (bit 0) is constant on R, i.e. b determined, and also column 2.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int W = atoi(argv[1]); const char *w = argv[2]; int maxit = argc > 3 ? atoi(argv[3]) : 100000;
    int p = strlen(w);
    uint64_t N = 1ULL << W, mask = N - 1;
    size_t words = (N + 63) / 64;
    uint64_t *R = malloc(words * 8), *S = malloc(words * 8);
    uint64_t **hist = calloc(p, sizeof(uint64_t*));
    memset(R, 0xff, words * 8);
    if (N % 64) R[words-1] &= (1ULL << (N % 64)) - 1;
    long t = 0;
    for (;;) {
        int ph = t % p;
        // check stabilization: compare R with hist[ph]
        if (hist[ph] && memcmp(hist[ph], R, words * 8) == 0) break;
        if (!hist[ph]) hist[ph] = malloc(words * 8);
        memcpy(hist[ph], R, words * 8);
        if (t > maxit) { printf("no stabilization by %ld\n", t); break; }
        uint64_t d = w[ph] - '0';
        memset(S, 0, words * 8);
        for (size_t k = 0; k < words; k++) {
            uint64_t m = R[k];
            while (m) {
                int b = __builtin_ctzll(m); m &= m - 1;
                uint64_t s = ((uint64_t)k << 6) | b;
                uint64_t left = ((s << 1) | d) & mask;
                uint64_t r0 = (s >> 1), r1 = (s >> 1) | (1ULL << (W - 1));
                uint64_t n0 = (left ^ (s | r0)) & mask, n1 = (left ^ (s | r1)) & mask;
                S[n0 >> 6] |= 1ULL << (n0 & 63); S[n1 >> 6] |= 1ULL << (n1 & 63);
            }
        }
        uint64_t *tmp = R; R = S; S = tmp;
        t++;
    }
    printf("W=%d w=%s stabilized at t=%ld (phase %ld)\n", W, w, t, t % p);
    // For each phase, report count and whether column 1 is determined
    for (int ph = 0; ph < p; ph++) {
        uint64_t *H = hist[ph]; uint64_t cnt = 0, c1 = 0, c2one = 0;
        for (size_t k = 0; k < words; k++) { cnt += __builtin_popcountll(H[k]); }
        // count states with bit0 = 1
        for (uint64_t s = 0; s < N; s++) if ((H[s >> 6] >> (s & 63)) & 1) { if (s & 1) c1++; if (s & 2) c2one++; }
        printf("  phase %d c=%c: |R|=%llu  col1=1 in %llu  col2=1 in %llu  -> col1 %s\n", ph, w[ph], (unsigned long long)cnt,
               (unsigned long long)c1, (unsigned long long)c2one, c1 == 0 ? "ALWAYS 0" : (c1 == cnt ? "ALWAYS 1" : "free"));
    }
    return 0;
}
