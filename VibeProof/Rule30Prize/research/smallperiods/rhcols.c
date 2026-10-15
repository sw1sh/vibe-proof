// Right half driven by periodic word w; print columns 1..K for times [t0, t1)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int W0 = atoi(argv[2]); long t0 = atol(argv[3]), t1 = atol(argv[4]); unsigned seed = atoi(argv[5]); int K = atoi(argv[6]);
    int p = strlen(w);
    long maxw = W0 + t1 + 2;
    uint8_t *a = calloc(maxw + 2, 1), *b = calloc(maxw + 2, 1);
    srand(seed);
    for (int i = 1; i <= W0; i++) a[i] = rand() & 1;
    a[W0] = 1;
    long wid = W0;
    for (long t = 0; t < t1; t++) {
        a[0] = w[t % p] - '0';
        if (t >= t0) { printf("%6ld %c|", t, a[0] ? '1' : '0'); for (int k = 1; k <= K; k++) putchar(a[k] ? '#' : '.'); putchar('\n'); }
        wid++;
        for (long i = 1; i <= wid; i++) b[i] = a[i-1] ^ (a[i] | a[i+1]);
        uint8_t *tmp = a; a = b; b = tmp;
    }
    return 0;
}
