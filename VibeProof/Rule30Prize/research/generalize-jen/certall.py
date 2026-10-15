import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/generalize-jen')
from certgen import find
n1, n2, Kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
for n in range(n1, n2 + 1):
    words = []
    for line in open(f's{n}.txt'):
        f = line.split()
        if f[1] != 'none': words.append((f[0], f[1] + (' ' + f[2] if f[1] == 'E' else '')))
    for w, tag in words:
        r = find([int(c) for c in w], Kmax=Kmax)
        print(n, w, tag, r, flush=True)
