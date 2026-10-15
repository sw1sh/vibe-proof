// Verifier: all-input closure size of the width-b projection of the worker's seed state
// (empty right half, column 0 = 1 at t = 0 then 001 repeating; state taken at T0), capped at CAP.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define CAP 5000001L
static uint64_t *hk; static uint8_t *hu; static size_t hc = 1ULL << 24;
static size_t hf(uint64_t k) { k ^= k >> 31; k *= 0x9E3779B97F4A7C15ULL; k ^= k >> 29; return (size_t)k & (hc - 1); }
static int hins(uint64_t k) { size_t i = hf(k); while (hu[i]) { if (hk[i] == k) return 0; i = (i + 1) & (hc - 1); } hu[i] = 1; hk[i] = k; return 1; }
int main(int argc, char **argv) {
    int T0 = atoi(argv[1]); const int w[3] = {0, 0, 1};
    static uint64_t row[64], nr[64]; int nw = 1;    // bit i = column i+1
    for (int t = 0; t < T0; t++) {
        int c = (t == 0) ? 1 : w[(t - 1) % 3];
        row[nw] = 0; uint64_t carry = (uint64_t)c; int nn = nw + 1;
        for (int j = 0; j < nn; j++) { uint64_t x = row[j], l = (x << 1) | carry, r = (x >> 1) | (j + 1 < nn ? row[j + 1] << 63 : 0); carry = x >> 63; nr[j] = l ^ (x | r); }
        memcpy(row, nr, 8 * (size_t)nn); nw = nn > 60 ? 60 : nn;   // only the first 64 columns are needed here
    }
    int ph0 = (T0 - 1) % 3;   // driver at time T0 is w[(T0-1) % 3]
    hk = malloc(8 * hc); hu = calloc(hc, 1); uint64_t *st = malloc(8 * (size_t)CAP);
    for (int ai = 2; ai < argc; ai++) {
        int b = atoi(argv[ai]); uint64_t mask = (b == 64) ? ~0ULL : ((1ULL << b) - 1);
        memset(hu, 0, hc); long n = 0, sp = 0;
        uint64_t s0 = ((row[0] & mask) << 2) | (uint64_t)ph0; hins(s0); st[sp++] = s0; n = 1;
        while (sp && n < CAP) {
            uint64_t v = st[--sp]; uint64_t r = v >> 2; int f = (int)(v & 3);
            for (int z = 0; z < 2 && n < CAP; z++) {
                uint64_t s = (((r << 1) | (uint64_t)w[f]) ^ (r | (r >> 1) | ((uint64_t)z << (b - 1)))) & mask;
                uint64_t k = (s << 2) | (uint64_t)((f + 1) % 3);
                if (hins(k)) { st[sp++] = k; n++; }
            }
        }
        printf("T0=%d b=%d: closure %s%ld states (state space %s)\n", T0, b, n >= CAP ? ">= " : "", n, b <= 40 ? "3*2^b" : "huge");
        fflush(stdout);
    }
    return 0;
}
