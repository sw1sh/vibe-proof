# End-to-end falsification test of the mechanism behind Theorem B':
# right half (columns 1..W) at time 0 arbitrary (random / adversarial), column 0 driven by the
# periodic word (1^r u)^inf starting at time 0. Claim implied by the proof: column 1 is P-periodic
# from time r on (P = r + |u|), for EVERY initial right-half state, whenever r >= max(9, 9 j0(u)).
# Uses big-int bitsets; row bit i = column i+1; light cone shrinks one cell per step.
import itertools, random, sys, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-bprime-cx')
from det_check import min_j0

def col1_trace(word, row_bits, N):
    """column 1 at times 0..N given driver word (periodic) and initial row of width N+1."""
    P = len(word)
    w = N + 1
    row = row_bits & ((1 << w) - 1)
    out = []
    for t in range(N):
        out.append(row & 1)
        l = word[t % P]
        left = (row << 1) | l
        right = row >> 1
        w -= 1
        row = (left ^ (row | right)) & ((1 << w) - 1)
    out.append(row & 1)
    return out

def periodic_from(tr, P, start):
    for t in range(start, len(tr) - P):
        if tr[t + P] != tr[t]:
            return False, t
    return True, None

def blocks(maxlen=7):
    for n in range(1, maxlen + 1):
        for bits in itertools.product((0, 1), repeat=n):
            if bits[0] == 0 and bits[-1] == 0:
                yield bits

if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    extra = [int(x) for x in (sys.argv[3].split(',') if len(sys.argv) > 3 else ['0', '1', '5', '17'])]
    t0 = time.time()
    total = 0; fails = 0
    for u in blocks():
        j0 = min_j0(u)
        rmin = max(9, 9 * j0)
        for dr in extra:
            r = rmin + dr
            word = [1] * r + list(u)
            P = len(word)
            N = 6 * P + 200
            inits = [0, (1 << (N + 1)) - 1]  # all white / all black
            inits += [int(''.join(random.choice('01') for _ in range(N + 1)), 2) for _ in range(trials)]
            # periodic adversarial initial rows
            for pat in ['01', '10', '0110', '0011', '1101000']:
                s = (pat * ((N + 1) // len(pat) + 1))[:N + 1]
                inits.append(int(s[::-1], 2))
            for x in inits:
                tr = col1_trace(word, x, N)
                ok, where = periodic_from(tr, P, r)
                total += 1
                if not ok:
                    fails += 1
                    if fails < 10:
                        print('FAIL u=', ''.join(map(str, u)), 'r=', r, 'first violation t=', where)
    print(f'total runs {total}, failures {fails}, time {time.time()-t0:.1f}s')
