// Falsification test: simulate a strip of width WW (columns 1..WW, byte arrays, no bit tricks) driven by
// column 0 = w[k mod p] with column WW+1 random each step, from random initial states. For k >= k0 and
// phases phi with w[phi]=='0', check column 1 equals the certified value pat[phi].
// usage: randsim w pat k0 WW steps trials seed
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint64_t rs;
static int rbit(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (int)(rs >> 63); }
int main(int argc, char **argv) {
    const char *w = argv[1], *pat = argv[2]; long k0 = atol(argv[3]); int WW = atoi(argv[4]);
    long steps = atol(argv[5]); long trials = atol(argv[6]); rs = 0x9E3779B97F4A7C15ull ^ (uint64_t)atoll(argv[7]);
    int p = (int)strlen(w);
    uint8_t *a = malloc(WW + 2), *b = malloc(WW + 2);
    long checks = 0, viol = 0;
    for (long tr = 0; tr < trials; tr++) {
        // vary the bias of the random input across trials
        int mode = (int)(tr % 4);
        for (int i = 1; i <= WW; i++) a[i] = (uint8_t)(mode == 0 ? 0 : mode == 1 ? 1 : rbit());
        for (long k = 0; k < steps; k++) {
            int ph = (int)(k % p);
            if (k >= k0 && w[ph] == '0') { checks++; if (a[1] != pat[ph] - '0') viol++; }
            a[0] = (uint8_t)(w[ph] - '0');
            int x;
            if (mode == 2) x = rbit() & rbit(); else if (mode == 3) x = rbit() | rbit(); else x = rbit();
            a[WW + 1] = (uint8_t)x;
            for (int i = 1; i <= WW; i++) b[i] = a[i - 1] ^ (a[i] | a[i + 1]);
            for (int i = 1; i <= WW; i++) a[i] = b[i];
        }
    }
    printf("%s WW=%d k0=%ld checks=%ld violations=%ld\n", w, WW, k0, checks, viol);
    return 0;
}
