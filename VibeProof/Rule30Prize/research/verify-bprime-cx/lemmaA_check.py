# Lemma A core: all 2^11 rows, 9 steps with black left neighbour -> [white, black].
# Lemma A*: random rows, column m black for 9j steps -> (white black)^j in next 2j columns.
# Also check the threshold sharpness: 8 black steps is NOT enough (sanity), and 9j-1 not enough for A*.
import itertools, random, sys
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/verify-bprime-cx')
from det_check import stepRow

def runBlack(k, L):
    for _ in range(k):
        L = stepRow(1, L)
    return L

bad = 0
for bits in itertools.product((0, 1), repeat=11):
    if runBlack(9, list(bits)) != [0, 1]:
        bad += 1
print('Lemma A core failures over 2^11 rows:', bad)

# sharpness: with 8 black steps (row length 10 -> 2 cells), is the result forced?
res8 = set(tuple(runBlack(8, list(b))) for b in itertools.product((0, 1), repeat=10))
print('8 black steps, possible (col m+1, col m+2):', sorted(res8))

# Lemma A*: rows of width 2j + 9j, run 9j black steps -> first 2j cells == (01)^j
random.seed(1)
for j in range(1, 7):
    w = 2 * j + 9 * j
    fails = 0
    trials = 20000 if j <= 4 else 5000
    for _ in range(trials):
        row = [random.randint(0, 1) for _ in range(w)]
        out = runBlack(9 * j, row)
        if out != [0, 1] * j:
            fails += 1
    # adversarial-ish: structured rows (all 0, all 1, periodic patterns)
    struct_fail = 0
    for pat in ['0', '1', '01', '10', '001', '011', '110', '0001', '0111', '00111', '1101000']:
        row = [int(pat[i % len(pat)]) for i in range(w)]
        if runBlack(9 * j, row) != [0, 1] * j:
            struct_fail += 1
    print(f'Lemma A* j={j}: random fails {fails}/{trials}, structured fails {struct_fail}')

# Sharpness of A*: 9j - 1 steps with j=2 -> is (0101) forced?
j = 2
w = 2 * j + 9 * j - 1
outs = set()
for _ in range(20000):
    row = [random.randint(0, 1) for _ in range(w)]
    outs.add(tuple(runBlack(9 * j - 1, row)))
print('9j-1 = 17 steps, j=2: distinct outputs', len(outs), '(1 would mean forced)')
