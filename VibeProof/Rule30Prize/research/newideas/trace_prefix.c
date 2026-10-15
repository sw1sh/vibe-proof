// Maximal periodic-trace prefix for finite rule-30 configurations of support radius w.
// Target trace: c(s) = word[s mod P] for s >= 0 (column 0 of a configuration X supported on [-w, w]).
// For each right half R = X(1..w) the left half making the trace equal to c for all s <= w is forced;
// it equals the left reconstruction (left-permutive) from columns 0 (= c) and -1, where
// col_{-1}(s) = c(s+1) xor (c(s) or col_1(s)) and col_1 is the right half driven by c.
// The configuration with that left half truncated to [-w,-1] has trace = c exactly up to time H-1,
// where H = first n > w with reconstructed col_{-n}(0) = 1.  We report max_R H and the argmax count.
// (Configurations whose trace deviates before time w+1 have shorter prefixes, so this is the true max
//  whenever the max exceeds w.)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int main(int argc, char **argv) {
    const char *word = argv[1]; int P = strlen(word);
    int w0 = atoi(argv[2]), w1 = atoi(argv[3]);
    for (int w = w0; w <= w1; w++) {
        int Tmax = 127 - w; if (Tmax > 120) Tmax = 120;
        int c[256]; for (int s = 0; s < 256; s++) c[s] = word[s % P] - '0';
        u128 cmask = 0; for (int s = 0; s <= Tmax; s++) if (c[s]) cmask |= (u128)1 << s;
        int best = -1; long long nbest = 0; long long hist[130]; memset(hist, 0, sizeof hist);
        u128 wmask = (w + Tmax >= 128) ? ~(u128)0 : (((u128)1 << (w + Tmax)) - 1);
        for (uint64_t R = 0; R < (1ULL << w); R++) {
            // right half: bit i <-> position i+1
            u128 row = (u128)R; u128 col1 = 0;
            for (int s = 0; s <= Tmax; s++) {
                if (row & 1) col1 |= (u128)1 << s;
                u128 leftn = (row << 1) | (u128)c[s];
                u128 rightn = row >> 1;
                row = (leftn ^ (row | rightn)) & wmask;
            }
            // col_{-1}(s) for s in [0, Tmax-1]
            u128 cm1 = 0;
            for (int s = 0; s < Tmax; s++) {
                int v = c[s + 1] ^ (c[s] | (int)((col1 >> s) & 1));
                if (v) cm1 |= (u128)1 << s;
            }
            // left reconstruction: x_{n+1} = (x_n >> 1) ^ (x_n | x_{n-1}); x_0 = c, x_1 = col_{-1}
            u128 xa = cmask, xb = cm1; int H = Tmax;  // xb = x_n with n = 1
            int n = 1; int found = 0;
            // x_n(0) for n <= w is unconstrained
            while (n < Tmax) {
                if (n > w && (xb & 1)) { H = n; found = 1; break; }
                u128 xn = (xb >> 1) ^ (xb | xa);
                xa = xb; xb = xn; n++;
            }
            if (!found) H = Tmax;  // lower bound
            if (H > best) { best = H; nbest = 1; } else if (H == best) nbest++;
            hist[H < 129 ? H : 129]++;
        }
        printf("word=%s w=%d  maxPrefix=%d (#R=%lld)  ratio=%.3f   top:", word, w, best, nbest, (double)best / w);
        int shown = 0; for (int h = 129; h >= 0 && shown < 5; h--) if (hist[h]) { printf(" %d:%lld", h, hist[h]); shown++; }
        printf("\n"); fflush(stdout);
    }
    return 0;
}
