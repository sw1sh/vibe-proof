# Exact word problem for G2369 = <a,b,c>, a = s(b,a), b = s(c,a), c = (c,a), with c = Phi (rule 30).
# Generators c, h = b^-1 c, k = a^-1 b:  c = (c, c.h.k), h = s(k.h, h.k), k = (h, 1);  D = <h,k> = D4.
# Convention: g(xw) = pi_g(x) g|_x(w), words compose right to left: (g h)(v) = g(h(v)).
import itertools

def dmul(x, y):  # D4 as rho^i kappa^j, rho = k h, kappa = k
    (i1, j1), (i2, j2) = x, y
    return ((i1 + (i2 if j1 == 0 else -i2)) % 4, (j1 + j2) % 2)
E, K, H = (0, 0), (0, 1), (3, 1)
assert dmul(H, H) == E and dmul(K, K) == E and dmul(K, H) == (1, 0)
DEL = [(i, j) for i in range(4) for j in range(2)]
def dinv(x):
    return ((-x[0]) % 4, 0) if x[1] == 0 else x
KH, HK = dmul(K, H), dmul(H, K)
# self-similar data of the generators of D: (root perm bit, section at 0, section at 1)
GEN = {K: (0, H, E), H: (1, KH, HK)}
def ddata_word(word):  # word = list of D generators, composed right to left
    out = {}
    for x in (0, 1):
        y, secs = x, []
        for g in reversed(word):
            pi, s0, s1 = GEN[g]
            secs.append(s0 if y == 0 else s1)
            y ^= pi
        s = E
        for t in reversed(secs):  # secs were collected right to left
            s = dmul(t, s) if False else s
        # rebuild left-to-right product
        prod = E
        for t in reversed(secs):
            prod = dmul(prod, t)
        out[x] = (y, prod)
    return out
# words for each element of D
WORDS = {E: []}
frontier = [E]
while frontier:
    nxt = []
    for d in frontier:
        for g in (H, K):
            e = dmul(d, g)
            if e not in WORDS:
                WORDS[e] = WORDS[d] + [g]; nxt.append(e)
    frontier = nxt
assert len(WORDS) == 8
DTAB = {}
for d, w in WORDS.items():
    o = ddata_word(w)
    pi = o[0][0] ^ 0
    assert (o[0][0] ^ 0) == pi and (o[1][0] ^ 1) == pi  # root perm acts uniformly
    DTAB[d] = (pi, (o[0][1], o[1][1]))
# consistency: section data is a homomorphism-compatible table
for d1 in DEL:
    for d2 in DEL:
        p = dmul(d1, d2)
        for x in (0, 1):
            y = x ^ DTAB[d2][0]
            assert dmul(DTAB[d1][1][y], DTAB[d2][1][x]) == DTAB[p][1][x]

def normalize(tokens):  # tokens: ('d', D) / ('c', +-1)  -> (d0, e1, d1, ..., el, dl)
    res = [E]
    for kind, v in tokens:
        if kind == 'd':
            res[-1] = dmul(res[-1], v)
        elif len(res) >= 3 and res[-2] == -v and res[-1] == E:
            res.pop(); res.pop()
        else:
            res.append(v); res.append(E)
    return tuple(res)

def rootperm(w):
    r = 0
    for idx in range(0, len(w), 2):
        r ^= DTAB[w[idx]][0]
    return r

def section(w, x):
    y, pieces = x, []
    for idx in range(len(w) - 1, -1, -1):
        it = w[idx]
        if idx % 2 == 0:
            pieces.append([('d', DTAB[it][1][y])]); y ^= DTAB[it][0]
        elif it == 1:
            pieces.append([('c', 1)] if y == 0 else [('c', 1), ('d', HK)])
        else:
            pieces.append([('c', -1)] if y == 0 else [('d', KH), ('c', -1)])
    toks = [t for p in reversed(pieces) for t in p]
    return y, normalize(toks)

def is_trivial(w, limit=2_000_000):
    seen, stack = {w}, [w]
    while stack:
        u = stack.pop()
        if rootperm(u):
            return False
        for x in (0, 1):
            _, s = section(u, x)
            if s not in seen:
                seen.add(s); stack.append(s)
                if len(seen) > limit:
                    raise RuntimeError('limit')
    return True

# words in a, b, c (and inverses A, B, C): a = c h k, b = c h
LET = {'c': [('c', 1)], 'C': [('c', -1)], 'a': [('c', 1), ('d', H), ('d', K)],
       'A': [('d', K), ('d', H), ('c', -1)], 'b': [('c', 1), ('d', H)], 'B': [('d', H), ('c', -1)],
       'h': [('d', H)], 'k': [('d', K)]}
def elt(s):
    return normalize([t for ch in s for t in LET[ch]])
