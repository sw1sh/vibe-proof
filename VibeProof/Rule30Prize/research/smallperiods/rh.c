// Right half driven by periodic word w from a random initial config of width W0; output column k sequence for `steps` steps.
// Uses a big bit array; the right half grows by 1 per step.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    const char *w = argv[1]; int W0 = atoi(argv[2]); long steps = atol(argv[3]); unsigned seed = atoi(argv[4]); int k = atoi(argv[5]);
    int p = strlen(w);
    long maxw = W0 + steps + 2;
    uint8_t *a = calloc(maxw + 2, 1), *b = calloc(maxw + 2, 1);
    srand(seed);
    for (int i = 1; i <= W0; i++) a[i] = rand() & 1;
    a[W0] = 1;
    long wid = W0;
    for (long t = 0; t < steps; t++) {
        putchar('0' + a[k]);
        a[0] = w[t % p] - '0';
        wid++;
        for (long i = 1; i <= wid; i++) b[i] = a[i-1] ^ (a[i] | a[i+1]);
        uint8_t *tmp = a; a = b; b = tmp;
        a[0] = 0;
    }
    putchar('\n');
    return 0;
}
