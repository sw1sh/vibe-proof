# Informational: minimal forbidden pair-words (offset-0 / prefix language) up to 12 pairs,
# from the regenerated 24-word set (all right-half windows, alternating center from a c=0 time).
import itertools
W = [l.strip() for l in open('w01_24_regen.txt') if l.strip()]
name = {'00': 'A', '01': 'B', '11': 'C', '10': 'X'}
pw = {''.join(name[w[o:o+2]] for o in range(0, 24, 2)) for w in W}
assert all('X' not in p for p in pw)
pref = set()
for p in pw:
    for n in range(0, 13): pref.add(p[:n])
mf = []
for n in range(1, 13):
    for tup in itertools.product('ABC', repeat=n):
        w = ''.join(tup)
        if w in pref: continue
        if (n == 1 or (w[1:] in pref and w[:-1] in pref)): mf.append(w)
print('minimal forbidden pair-words up to length 12:', mf)
print('number of admissible 12-pair words:', len(pw))
