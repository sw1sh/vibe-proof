# Independent check of C5(d): column-1 words of the right half driven by an alternating
# center column 0,1,0,1,... starting at a c=0 time s, over ALL right-half windows.
# b(s+k) = cell(s+k, 1) depends only on c(s..s+k-1) and cells (s, 1..1+k), so the
# set of achievable words of length L is obtained from all 2^L windows (columns 1..L).
import itertools, sys

def rule(l, c, r):
    return l ^ (c | r)

def driven_col1(window, cvals):
    """window = cells at columns 1..W at time s; cvals = c(s), ..., c(s+m-1).
    Returns b(s), ..., b(s+m). Requires W >= m+1 (shrinking light cone)."""
    row = list(window)
    out = [row[0]]
    for cv in cvals:
        new = []
        for i in range(len(row) - 1):
            left = cv if i == 0 else row[i - 1]
            new.append(rule(left, row[i], row[i + 1]))
        row = new
        out.append(row[0])
    return out

def words(L):
    cvals = [k % 2 for k in range(L - 1)]   # c(s..s+L-2) = 0,1,0,1,...
    S = set()
    for w in itertools.product((0, 1), repeat=L):
        S.add(tuple(driven_col1(w, cvals)))
    return S

P = {'A': (0, 0), 'B': (0, 1), 'C': (1, 1)}
def bits(pw):
    return tuple(x for ch in pw for x in P[ch])

def occurs_even(S, pat):
    n = len(pat)
    return any(w[o:o + n] == pat for w in S for o in range(0, len(w) - n + 1, 2))

def occurs_odd(S, pat):
    n = len(pat)
    return any(w[o:o + n] == pat for w in S for o in range(1, len(w) - n + 1, 2))

L = int(sys.argv[1]) if len(sys.argv) > 1 else 14
S = words(L)
print('L =', L, ' #achievable words =', len(S))
print('pair 10 at even offset occurs:', occurs_even(S, (1, 0)))
for pw in ['AA', 'BB', 'BC', 'CC', 'ABAB', 'ACBACA', 'CACBAC', 'ACACACB']:
    pat = bits(pw)
    if len(pat) <= L:
        print(f'{pw:8s} even-offset occurs: {occurs_even(S, pat)}   (odd-offset occurs: {occurs_odd(S, pat)})')
# controls: some pair words that should occur
for pw in ['AB', 'BA', 'AC', 'CA', 'CB', 'ABA', 'BAB', 'ACBA', 'ACACAC', 'ACBACB']:
    pat = bits(pw)
    if len(pat) <= L:
        print(f'control {pw:8s} occurs: {occurs_even(S, pat)}')
# minimality: does each exclusion fail without the alternation length used? (window widths)
with open(f'/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-C5-rigor/S{L}.txt', 'w') as f:
    for w in sorted(S):
        f.write(''.join(map(str, w)) + '\n')
