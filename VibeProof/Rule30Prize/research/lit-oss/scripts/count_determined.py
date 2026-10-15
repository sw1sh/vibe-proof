import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/lit-oss/scripts')
from verify_word_exclusions import one_sided_determined
def lyndon_words(n):
    # Duval's algorithm generating Lyndon words of length exactly n over {0,1}
    w = [-1]
    while w:
        w[-1] += 1
        m = len(w)
        if m == n:
            yield tuple(w)
        while len(w) < n:
            w.append(w[len(w) - m])
        while w and w[-1] == 1:
            w.pop()
K = int(sys.argv[1]); lo = int(sys.argv[2]); hi = int(sys.argv[3])
for p in range(lo, hi + 1):
    cnt = 0; tot = 0; dets = []
    for w in lyndon_words(p):
        tot += 1
        ok, col, sz = one_sided_determined(list(w), K)
        if ok:
            cnt += 1; dets.append(''.join(map(str, w)))
    print(f"p={p} K={K}: Lyndon words={tot} determined={cnt}")
    if cnt <= 12: print("   ", dets)
