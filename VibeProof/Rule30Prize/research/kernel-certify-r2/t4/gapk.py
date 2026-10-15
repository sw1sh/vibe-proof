import sys, itertools
sys.argv = sys.argv  # w b L K
exec(open('badscc.py').read().split("w = sys.argv[1]\nfor b in")[0])
from collections import defaultdict
w = sys.argv[1]; b = int(sys.argv[2]); L = int(sys.argv[3]); K = int(sys.argv[4])
r = analyze(w, b, L, K)
print({k: v for k, v in r.items() if k != 'forb2'}, 'forb2', r.get('forb2'))
