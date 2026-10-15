import sys, subprocess
W0 = int(sys.argv[1]); steps = int(sys.argv[2]); seed = int(sys.argv[3])
s = subprocess.run(['./rh', '01', str(W0), str(steps), str(seed), '1'], capture_output=True, text=True).stdout.strip()
pairs = [s[i:i+2] for i in range(0, len(s) - 1, 2)]
sym = ''.join({'00':'A','01':'B','11':'C','10':'?'}[p] for p in pairs)
# skip transient: start at first 'C' after position 40
i0 = sym.index('C', 40)
body = sym[i0:]
xy = []
i = 0
while i + 3 <= len(body):
    if body[i:i+3] == 'CBA': xy.append('X'); i += 3
    elif body[i:i+2] == 'BA': xy.append('Y'); i += 2
    else: break
xs = ''.join(xy)
print(len(xs))
print(xs[:600])
for n in [1,2,3,4,5,6,8,10,12,16,20,24,32]:
    print(n, len(set(xs[j:j+n] for j in range(len(xs)-n))), end='; ')
print()
# run-lengths of Y between X's
import re
runs = [len(m) for m in re.findall(r'X(Y*)', xs)]
from collections import Counter
print('Y-run lengths', Counter(runs))
