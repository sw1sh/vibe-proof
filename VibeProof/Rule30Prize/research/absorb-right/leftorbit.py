# Leftward orbit of a shield column sigma (period Q) with forced values f at its zero phases:
# x(t, p-1) = x(t+1, p) xor (x(t,p) or x(t,p+1)); at zero phases of sigma the right neighbour is f.
import sys
def lyndon_rep(s):
    # minimal rotation, and its primitive root
    n = len(s)
    for d in range(1, n + 1):
        if n % d == 0 and s == s[:d] * (n // d):
            s = s[:d]; break
    return min(s[i:] + s[:i] for i in range(len(s)))
def orbit(sigma, f, steps):
    Q = len(sigma)
    cur = [int(ch) for ch in sigma]                 # column m
    right = [f[r] if cur[r] == 0 else 0 for r in range(Q)]  # column m+1 where it matters
    cols = [cur]
    prev_right = right
    for d in range(1, steps + 1):
        new = [cur[(r + 1) % Q] ^ (cur[r] | prev_right[r]) for r in range(Q)]
        prev_right = cur; cur = new; cols.append(cur)
    return cols
if __name__ == "__main__":
    sigma = sys.argv[1]; f = {int(k): int(v) for k, v in (x.split(':') for x in sys.argv[2].split(','))}
    steps = int(sys.argv[3])
    cols = orbit(sigma, f, steps)
    for d, c in enumerate(cols):
        s = ''.join(map(str, c))
        print(f"distance {d:3d}: {s}  primitive necklace {lyndon_rep(s)}")
