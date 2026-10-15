import sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/lit-oss/scripts')
from verify_word_exclusions import two_sided_check
r = int(sys.argv[1])
for s in sys.argv[2:]:
    w = [int(ch) for ch in s]
    okm, infom = two_sided_check(w, r, -1)
    okp, infop = two_sided_check(w, r, +1)
    print(f"{s}: r={r} col-1 forced={okm} {infom} | col+1 forced={okp} {infop}")
