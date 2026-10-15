// Safety game: outer strip y_1..y_m (columns k+1..k+m) driven on the left by periodic d(phase) (period Pd),
// free (adversarial) input at column m+1. Bad: at phase phi0, y_1 != v.
// Compute greatest closed safe set. State: (phase, y bits). bit i <-> y_{i+1}.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    int m = atoi(argv[1]);
    const char *dstr = argv[2]; // driver string, period = strlen
    int phi0 = atoi(argv[3]);   // phase where y_1 must equal v
    int v = atoi(argv[4]);
    int Pd = strlen(dstr);
    uint64_t N = 1ULL << m;
    uint8_t *safe = malloc(Pd * N);
    for (int ph = 0; ph < Pd; ph++) for (uint64_t s = 0; s < N; s++)
        safe[ph*N + s] = (ph == phi0) ? (((s & 1) == (uint64_t)v) ? 1 : 0) : 1;
    uint64_t mask = N - 1;
    int changed = 1, iter = 0;
    while (changed) {
        changed = 0; iter++;
        for (int ph = 0; ph < Pd; ph++) {
            int d = dstr[ph] - '0';
            int nph = (ph + 1) % Pd;
            for (uint64_t s = 0; s < N; s++) {
                if (!safe[ph*N + s]) continue;
                // successors for x in {0,1}
                for (int x = 0; x < 2; x++) {
                    uint64_t left = ((s << 1) | d) & mask;      // y_{i-1}
                    uint64_t right = (s >> 1) | ((uint64_t)x << (m-1)); // y_{i+1}
                    uint64_t ns = (left ^ (s | right)) & mask;
                    if (!safe[nph*N + ns]) { safe[ph*N + s] = 0; changed = 1; break; }
                }
            }
        }
    }
    uint64_t tot = 0;
    for (int ph = 0; ph < Pd; ph++) { uint64_t c = 0; for (uint64_t s = 0; s < N; s++) c += safe[ph*N+s]; printf("phase %d safe %llu\n", ph, (unsigned long long)c); tot += c; }
    printf("m=%d total safe %llu iters %d\n", m, (unsigned long long)tot, iter);
    return 0;
}
