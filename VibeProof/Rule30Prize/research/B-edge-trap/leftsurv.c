// Left-half survival: left half (columns -1, -2, ...) with column 0 = w^inf (phase ph0 at t=0), initial support in
// [-W, -1] (all 2^W configurations). The center column's update c(t+1) = cell(t,-1) xor (c(t) or cell(t,1)) forces
// cell(t,-1) = !c(t+1) whenever c(t) = 1.  Report the maximal survival time (first violation) over all configurations.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXW 64
int main(int argc, char **argv) {
    const char *w = argv[1]; int P = strlen(w); int W = atoi(argv[2]); long S = atol(argv[3]);
    long maxsurv = -1; uint32_t argx = 0; int argph = 0; long nsurv = 0; long hist[64] = {0};
    for (int ph0 = 0; ph0 < P; ph0++) {
        for (uint32_t x = 0; x < (1u << W); x++) {
            uint64_t a[MAXW]; int nw = 1; memset(a, 0, sizeof a);
            a[0] = ((uint64_t)x << 1) | (uint64_t)(w[ph0] - '0'); // bit q = cell(-q), bit 0 = c(t)
            long t = 0; long viol = -1;
            for (; t < S; t++) {
                int ph = (int)((ph0 + t) % P), c = w[ph] - '0', cn = w[(ph + 1) % P] - '0';
                int m1 = (int)((a[0] >> 1) & 1);
                if (c == 1 && m1 != !cn) { viol = t; break; }
                // evolve: new[q] = old[q+1] ^ (old[q] | old[q-1]) for q >= 1; bit 0 = next c
                if ((a[nw - 1] >> 60) != 0) { if (nw >= MAXW) break; a[nw++] = 0; }
                uint64_t prev_hi = 0, na[MAXW];
                for (int i = 0; i < nw; i++) {
                    uint64_t v = a[i];
                    uint64_t up = (v >> 1) | ((i + 1 < nw) ? (a[i + 1] << 63) : 0);   // old[q+1] at bit q
                    uint64_t down = (v << 1) | prev_hi;                                 // old[q-1] at bit q
                    prev_hi = v >> 63;
                    na[i] = up ^ (v | down);
                }
                memcpy(a, na, sizeof(uint64_t) * nw);
                a[0] = (a[0] & ~1ULL) | (uint64_t)cn;
            }
            if (viol < 0) { nsurv++; continue; }
            int bk = 0; long e = viol; while (e) { bk++; e >>= 1; } hist[bk]++;
            if (viol > maxsurv) { maxsurv = viol; argx = x; argph = ph0; }
        }
    }
    printf("w=%s W=%d: survivors past %ld steps: %ld; max violation time %ld (x=%u ph0=%d); log2hist:", w, W, S, nsurv, maxsurv, argx, argph);
    for (int i = 0; i < 64; i++) if (hist[i]) printf(" [%d]%ld", i, hist[i]);
    printf("\n");
    return 0;
}
