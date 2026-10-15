// Verifier: brute-force death times for driven left halves (independent of the worker's DFS).
// Depth i >= 1 is position -i; depth 0 is the boundary c'(t) = E[(ph0 + t) % 3].
// x_i(t+1) = x_{i+1}(t) xor (x_i(t) or x_{i-1}(t)).  Constraint: x_1(t) = K[(ph0 + t) % 3] unless '*'.
// Every start with L(1..W) arbitrary (2^W starts) is run until its first violation; prints, for each W in
// [W0, W1], the max first-violation time over all starts of width <= W. A start surviving HOR steps is reported.
// usage: mydeath E K ph0 W0 W1
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NWD 6
#define HOR 300
int main(int argc, char **argv) {
    const char *E = argv[1], *K = argv[2]; int ph0 = atoi(argv[3]), W0 = atoi(argv[4]), W1 = atoi(argv[5]);
    int best = 0;
    for (int W = 1; W <= W1; W++) {
        // starts of width exactly W have bit W-1 set (depth W black); smaller widths were covered earlier
        uint64_t lo = (W == 1) ? 0 : (1ULL << (W - 1)), hi = 1ULL << W;
        for (uint64_t s = lo; s < hi; s++) {
            uint64_t r[NWD] = {0}, f[NWD + 1], n[NWD];
            r[0] = s; int t = 0, words = (W + 63) / 64 + 1;
            for (;;) {
                int ph = (ph0 + t) % 3;
                if (K[ph] != '*' && (int)(r[0] & 1) != K[ph] - '0') break;      // first violation at time t
                if (t == HOR) { printf("SURVIVOR: W=%d start=%llu ph0=%d survives %d steps\n", W, (unsigned long long)s, ph0, HOR); break; }
                uint64_t c = (uint64_t)(E[ph] - '0');
                // f = (r << 1) | c  (bit k = depth k)
                uint64_t carry = c;
                for (int j = 0; j < words; j++) { f[j] = (r[j] << 1) | carry; carry = r[j] >> 63; }
                f[words] = carry;
                // new bit k (depth k+1) = f[k+2] ^ (f[k+1] | f[k])
                for (int j = 0; j < words; j++) {
                    uint64_t f1 = (f[j] >> 1) | (f[j + 1] << 63), f2 = (f[j] >> 2) | (f[j + 1] << 62);
                    n[j] = f2 ^ (f1 | f[j]);
                }
                memcpy(r, n, 8 * (size_t)words);
                t++;
                int need = (W + t + 2 + 63) / 64 + 1; if (need > words) { if (need > NWD - 1) { printf("too wide\n"); return 1; } for (int j = words; j < need; j++) r[j] = 0; words = need; }
            }
            if (t > best) best = t;
        }
        if (W >= W0) printf("E=%s K=%s ph0=%d W=%2d: brute max first-violation time %d\n", E, K, ph0, W, best);
        fflush(stdout);
    }
    return 0;
}
