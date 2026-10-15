import sys, random, subprocess
sys.path.insert(0, '.')
from core import recon_y
random.seed(7)
ys = []
for _ in range(300):
    n = random.randint(1, 250)
    ys.append([random.getrandbits(1) for _ in range(n)])
inp = '\n'.join(''.join(map(str, y)) for y in ys) + '\n'
out = subprocess.run(['./c/steptest'], input=inp.encode(), capture_output=True).stdout.decode().split()
bad = 0
for y, o in zip(ys, out):
    if ''.join(map(str, recon_y(y))) != o: bad += 1
print('compared', len(ys), 'mismatches', bad)
