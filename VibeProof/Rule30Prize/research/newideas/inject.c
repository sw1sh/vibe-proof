// Collisions of center traces among finite rule-30 configurations supported in [-w, w].
// For each configuration compute trace bits 0..H-1 (H <= 128) and look for equal traces.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef struct { uint64_t lo, hi; uint32_t id; } Rec;
static int cmp(const void *a, const void *b) {
    const Rec *x = a, *y = b;
    if (x->hi != y->hi) return x->hi < y->hi ? -1 : 1;
    if (x->lo != y->lo) return x->lo < y->lo ? -1 : 1;
    return 0;
}
int main(int argc, char **argv) {
    int w = atoi(argv[1]); int H = atoi(argv[2]);
    int n = 2 * w + 1; uint32_t N = 1u << n;
    Rec *recs = malloc(sizeof(Rec) * N);
    // row representation: 4 x 64-bit words, center at bit 128
    for (uint32_t x = 0; x < N; x++) {
        uint64_t r[4] = {0, 0, 0, 0};
        for (int i = 0; i < n; i++) if ((x >> i) & 1) { int pos = 128 - w + i; r[pos >> 6] |= 1ULL << (pos & 63); }
        uint64_t lo = 0, hi = 0;
        for (int t = 0; t < H; t++) {
            int bit = (r[2] >> 0) & 1;   // position 128
            if (t < 64) lo |= (uint64_t)bit << t; else hi |= (uint64_t)bit << (t - 64);
            uint64_t nr[4];
            for (int k = 0; k < 4; k++) {
                uint64_t L = (r[k] << 1) | (k ? r[k - 1] >> 63 : 0);   // value of p-1 at p  (bit i <- bit i-1)
                uint64_t R = (r[k] >> 1) | (k < 3 ? r[k + 1] << 63 : 0);
                nr[k] = L ^ (r[k] | R);
            }
            memcpy(r, nr, sizeof r);
        }
        recs[x].lo = lo; recs[x].hi = hi; recs[x].id = x;
    }
    qsort(recs, N, sizeof(Rec), cmp);
    long coll = 0; int shown = 0;
    for (uint32_t i = 1; i < N; i++) if (recs[i].lo == recs[i - 1].lo && recs[i].hi == recs[i - 1].hi) {
        coll++;
        if (shown < 6) {
            printf("collision: ");
            for (int j = n - 1; j >= 0; j--) putchar((recs[i - 1].id >> j) & 1 ? '#' : '.');
            printf("  vs  ");
            for (int j = n - 1; j >= 0; j--) putchar((recs[i].id >> j) & 1 ? '#' : '.');
            printf("\n"); shown++;
        }
    }
    printf("w=%d H=%d configs=%u collisions(adjacent equal pairs)=%ld\n", w, H, N, coll);
    return 0;
}
