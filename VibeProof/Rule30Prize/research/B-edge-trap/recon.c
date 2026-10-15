// Left reconstruction for c = w^inf: column 0 = w (phase ph0 at t=0), column -1 fixed to !c(t+1) at the black
// phases of c and free (bits f) at the white phases.  By left-permutivity
//   cell(t, -(m+1)) = cell(t+1, -m) xor (cell(t, -m) or cell(t, -(m-1)))
// every column -m over times [0, L-m] is a function of the free bits.  For each depth m report the longest white
// run (over all free-bit assignments, all positions) and the longest white run starting at time 0.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int P = strlen(w); int L = atoi(argv[2]); int ph0 = atoi(argv[3]); int M = atoi(argv[4]);
    // free positions in [0, L)
    int nfree = 0, freepos[64];
    for (int t = 0; t < L; t++) if (w[(ph0 + t) % P] == '0') freepos[nfree++] = t;
    if (nfree > 26) { fprintf(stderr, "too many free bits (%d)\n", nfree); return 1; }
    int *maxrun = calloc(M + 2, sizeof(int)), *maxrun0 = calloc(M + 2, sizeof(int));
    static uint8_t col[2][4096], prv[4096], cur[4096];
    for (uint32_t f = 0; f < (1u << nfree); f++) {
        // column 0 and -1 over [0, L]
        uint8_t c0[4096], c1[4096];
        for (int t = 0; t <= L; t++) c0[t] = w[(ph0 + t) % P] - '0';
        int fi = 0;
        for (int t = 0; t < L; t++) { if (c0[t]) c1[t] = !c0[t + 1]; else c1[t] = (f >> fi++) & 1; }
        // prv = column -(m-1), cur = column -m ; valid lengths decrease by one per depth
        memcpy(prv, c0, L + 1); memcpy(cur, c1, L);
        int len_prv = L + 1, len_cur = L;
        for (int m = 1; m <= M && len_cur > 1; m++) {
            // white runs in column -m over [0, len_cur)
            int run = 0, best = 0, run0 = 0, started = 1;
            for (int t = 0; t < len_cur; t++) { if (!cur[t]) { run++; if (run > best) best = run; if (started) run0 = run; } else { run = 0; started = 0; } }
            if (best > maxrun[m]) maxrun[m] = best;
            if (run0 > maxrun0[m]) maxrun0[m] = run0;
            // next column -(m+1) over [0, len_cur - 1)
            uint8_t nxt[4096];
            for (int t = 0; t + 1 < len_cur; t++) nxt[t] = cur[t + 1] ^ (cur[t] | prv[t]);
            memcpy(prv, cur, len_cur); len_prv = len_cur;
            memcpy(cur, nxt, len_cur - 1); len_cur = len_cur - 1;
        }
        (void)len_prv;
    }
    printf("w=%s L=%d ph0=%d free bits=%d\n depth m: max white run anywhere / max initial white run (window length L-m+1)\n", w, L, ph0, nfree);
    for (int m = 1; m <= M; m++) printf(" m=%d: %d/%d", m, maxrun[m], maxrun0[m]);
    printf("\n");
    return 0;
}
