# Check black-run forcing and the key identity cell(t,1) = !c(t-1) on the actual rule 30 pattern.
import sys
N = int(sys.argv[1])
row = 1 << N  # position p <-> bit p + N
c = []; col1 = []; col2 = []
for t in range(N):
    c.append((row >> N) & 1); col1.append((row >> (N + 1)) & 1); col2.append((row >> (N + 2)) & 1)
    row = (row << 1) ^ (row | (row >> 1))
# compare with the read-only data file (first value in high bit)
with open('/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin', 'rb') as f:
    data = f.read((N + 7) // 8)
ref = [(data[i // 8] >> (7 - i % 8)) & 1 for i in range(N)]
print('center column matches center-1e7.bin:', ref == c, ' first 20:', c[:20])
# forcing lemma instances
inst = bad = 0
for t in range(N - 9):
    if all(c[t + j] for j in range(9)):
        inst += 1
        if not (col1[t + 9] == 0 and col2[t + 9] == 1):
            bad += 1
print('runs of >=9 blacks (windows):', inst, ' violations of forcing:', bad)
# key identity at white times whose white run is preceded by >= 9 blacks
cnt = badk = 0
for t in range(20, N):
    if c[t] == 0:
        s = t
        while c[s - 1] == 0:
            s -= 1
        if s >= 9 and all(c[s - 1 - j] for j in range(9)):
            cnt += 1
            if col1[t] != 1 - c[t - 1]:
                badk += 1
print('white times after >=9-black run:', cnt, ' violations of cell(t,1) = !c(t-1):', badk)
# control: how often does the identity hold at OTHER white times (should not be always)
oth = ok = 0
for t in range(20, N):
    if c[t] == 0:
        s = t
        while c[s - 1] == 0:
            s -= 1
        if not (s >= 9 and all(c[s - 1 - j] for j in range(9))):
            oth += 1
            ok += (col1[t] == 1 - c[t - 1])
print('control: other white times', oth, ' identity holds at', ok)
