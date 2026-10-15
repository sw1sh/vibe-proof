# Parse column-1 sequence (driver 01, c(0)=0) into pair symbols A=00,B=01,C=11 and find the time after which it is a
# concatenation of X=CBA and Y=BA. Report max such transient over many seeds.
import sys, subprocess
W0 = int(sys.argv[1]); steps = int(sys.argv[2]); seeds = int(sys.argv[3])
maxtr = 0; other = {}
for seed in range(1, seeds + 1):
    s = subprocess.run(['./rh', '01', str(W0), str(steps), str(seed), '1'], capture_output=True, text=True).stdout.strip()
    pairs = [s[i:i+2] for i in range(0, len(s) - 1, 2)]
    sym = ''.join({'00':'A','01':'B','11':'C','10':'?'}[p] for p in pairs)
    # find last position where parse into CBA/BA fails, scanning from the end backwards is tricky; do forward greedy from each candidate start
    # simpler: find all occurrences of symbols patterns not allowed in the XY language: allowed 2-grams in (CBA|BA)^*: CB, BA, AC, AB ; 'A' followed by C or B; 'B' followed by A; 'C' followed by B.
    bad = [i for i in range(len(sym) - 1) if sym[i:i+2] not in ('CB', 'BA', 'AC', 'AB')]
    tr = (bad[-1] + 2) if bad else 0
    maxtr = max(maxtr, tr)
    # also count 'ABAB' (YY) occurrences after transient
    yy = sym[tr:].count('BABA')
    print('seed', seed, 'transient(pairs)', tr, 'YY count', yy, 'first syms', sym[:30], 'last bad bigrams', [sym[i:i+2] for i in bad[-3:]])
print('max transient pairs', maxtr)
