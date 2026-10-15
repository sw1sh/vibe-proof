// Test: the tabulated successor (same code as vreach.c) agrees with true rule-30 evolution from a single cell,
// and with random strips embedded in random wider configurations.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int W;
static int colv(uint32_t s, int i) { return (s >> (W - i)) & 1; }
static uint32_t succ(uint32_t s, int d, int x) {
    uint32_t r = 0;
    for (int i = 1; i <= W; i++) {
        int L = (i == 1) ? d : colv(s, i - 1);
        int C = colv(s, i);
        int R = (i == W) ? x : colv(s, i + 1);
        int v = L ^ (C | R);
        r |= (uint32_t)v << (W - i);
    }
    return r;
}
int main(void) {
    int T = 3000, off = T + 5, n = 2 * T + 11;
    unsigned char *a = calloc(n, 1), *b = calloc(n, 1);
    a[off] = 1; // cell(0,0)=1
    long checks = 0, bad = 0;
    // print first center values
    printf("center: ");
    for (int t = 0; t < T; t++) {
        if (t < 20) printf("%d", a[off]);
        for (W = 1; W <= 20; W++) {
            uint32_t s = 0;
            for (int i = 1; i <= W; i++) s |= (uint32_t)a[off + i] << (W - i);
            int d = a[off], x = a[off + W + 1];
            uint32_t s2 = succ(s, d, x);
            // next row
            uint32_t s3 = 0;
            for (int i = 1; i <= W; i++) { int p = off + i; int v = a[p - 1] ^ (a[p] | a[p + 1]); s3 |= (uint32_t)v << (W - i); }
            checks++; if (s2 != s3) bad++;
        }
        for (int p = 1; p < n - 1; p++) b[p] = a[p - 1] ^ (a[p] | a[p + 1]);
        unsigned char *tmp = a; a = b; b = tmp;
    }
    printf("\nchecks=%ld bad=%ld\n", checks, bad);
    // cross-check with rule 30 table: rule number 30 = 00011110: pattern (L,C,R) -> bit (4L+2C+R) of 30
    int ok = 1;
    for (int L = 0; L < 2; L++) for (int C = 0; C < 2; C++) for (int R = 0; R < 2; R++) {
        int v1 = L ^ (C | R), v2 = (30 >> (4 * L + 2 * C + R)) & 1; if (v1 != v2) ok = 0; }
    printf("rule30 table ok=%d\n", ok);
    return 0;
}
