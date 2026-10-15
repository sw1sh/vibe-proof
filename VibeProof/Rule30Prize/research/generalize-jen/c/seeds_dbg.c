#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(void) {
    int W = 1, N = 30, L = 2 * N + W + 4, off = N + 2;
    uint8_t *a = calloc(L, 1), *b = calloc(L, 1);
    a[off] = 1;
    for (int t = 0; t < N; t++) {
        putchar('0' + a[off]);
        int lo = off - t - 2, hi = off + W + t + 2;
        if (lo < 1) lo = 1; if (hi > L - 2) hi = L - 2;
        for (int i = lo; i <= hi; i++) b[i] = a[i - 1] ^ (a[i] | a[i + 1]);
        b[lo - 1] = 0; b[hi + 1] = 0;
        uint8_t *tmp = a; a = b; b = tmp;
    }
    putchar('\n');
}
