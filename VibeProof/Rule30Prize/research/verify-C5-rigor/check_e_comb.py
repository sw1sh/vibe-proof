# (e) combinatorics: in every word over {A,B,C} avoiding AA,BB,BC,CC,ABAB,
# consecutive C's are 2..5 pairs apart and every 5 consecutive letters contain C.
FORB = ['AA', 'BB', 'BC', 'CC', 'ABAB']
def ok(w): return not any(w.endswith(f) for f in FORB)
N = 18
level = ['']
gaps = set(); viol = 0; total = 0
for n in range(1, N + 1):
    nxt = []
    for w in level:
        for ch in 'ABC':
            v = w + ch
            if ok(v): nxt.append(v)
    level = nxt
for w in level:
    total += 1
    cs = [i for i, x in enumerate(w) if x == 'C']
    for a, b in zip(cs, cs[1:]):
        gaps.add(b - a)
    if any('C' not in w[i:i+5] for i in range(len(w) - 4)): viol += 1
print(f'length {N}: {total} admissible words; C-gaps (pairs) = {sorted(gaps)}; 5-windows without C: {viol}')
# also the stretch claim: maximal C-free factors between two C's
stretches = set()
for w in level:
    parts = w.split('C')
    for p in parts[1:-1]: stretches.add(p)
print('stretches between consecutive Cs:', sorted(stretches, key=len))
