// Strip relaxation at the trap width: random right inputs (i.i.d. fair bits) from random initial strips.
// How often (and how fast) does the strip enter the trap t001?  usage: rwalk47 trapfile runs maxsteps seed
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t *hk; static uint8_t *hu; static size_t cap;
static size_t hh(uint64_t k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; return (size_t)k & (cap - 1); }
static void put(uint64_t k) { size_t i = hh(k); while (hu[i]) { if (hk[i] == k) return; i = (i + 1) & (cap - 1); } hu[i] = 1; hk[i] = k; }
static int get(uint64_t k) { size_t i = hh(k); while (hu[i]) { if (hk[i] == k) return 1; i = (i + 1) & (cap - 1); } return 0; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char w[8]; int b, m; long n; if (fscanf(f, "%7s %d %d %ld", w, &b, &m, &n) != 4) return 1;
    cap = 1; while (cap < 4 * (size_t)n) cap <<= 1; hk = calloc(cap, 8); hu = calloc(cap, 1);
    for (long i = 0; i < n; i++) { unsigned long long r; int l; if (fscanf(f, "%llu %d", &r, &l) != 2) return 1; put(((uint64_t)r << 2) | (uint64_t)(l % 3)); }
    long runs = atol(argv[2]), maxs = atol(argv[3]); uint64_t rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[4]);
    uint64_t M = (1ULL << b) - 1; long hit = 0; double sum = 0; long mx = 0;
    for (long k = 0; k < runs; k++) {
        rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; uint64_t r = rs & M; int ph = (int)(k % 3);
        long t;
        for (t = 0; t < maxs; t++) {
            if (get((r << 2) | (uint64_t)ph)) break;
            rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; uint64_t z = rs & 1;
            uint64_t a = (uint64_t)(w[ph] - '0');
            unsigned __int128 full = (unsigned __int128)a | ((unsigned __int128)r << 1) | ((unsigned __int128)z << (b + 1));
            r = (uint64_t)((full ^ ((full >> 1) | (full >> 2))) & M); ph = (ph + 1) % 3;
        }
        if (t < maxs) { hit++; sum += t; if (t > mx) mx = t; }
    }
    printf("width %d, random right inputs: %ld/%ld runs enter t001 within %ld steps (mean %.0f, max %ld)\n", b, hit, runs, maxs, hit ? sum / hit : 0, mx);
    return 0;
}
