# Print the rigid 38-column core of the 001 trap over one period (21 labels), next to the ether.
import sys
rows = [tuple(map(int, l.split())) for l in open(sys.argv[1]).read().split('\n')[1:] if l.strip()]
core = {}
for (r, l) in rows:
    c = r & ((1 << 47) - 1)
    core.setdefault(l, set()).add(c & ((1 << 38) - 1))
E = ["001","001","011","110","010","010","110","101","100","100","101","011"]
w = "001"
for l in range(21):
    cs = core[l]; assert len(cs) == 1
    c = next(iter(cs))
    s = ''.join('#' if (c >> i) & 1 else '.' for i in range(38))
    col0 = '#' if w[l % 3] == '1' else '.'
    print(f"label {l:2d} phase {l%3}: {col0}|{s}")
# longest ether match: for each j0, s, count columns p=1.. where core equals ether3(j0+p, l+s) for all l
best = (0, (-1, -1))
for j0 in range(12):
    for sh in range(3):
        if any(E[j0][(l + sh) % 3] != w[l % 3] for l in range(3)): continue
        k = 0
        for p in range(1, 39):
            if all(((next(iter(core[l])) >> (p - 1)) & 1) == int(E[(j0 + p) % 12][(l + sh) % 3]) for l in range(21)): k = p
            else: break
        best = max(best, (k, (j0, sh)))
print("longest prefix of the core that is 12x3 ether (aligned with the center):", best)
