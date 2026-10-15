import sys
P = {'A': '00', 'B': '01', 'C': '11'}
W = [l.strip() for l in open(sys.argv[1]) if l.strip()]
assert all(len(w) == 24 and set(w) <= {'0','1'} for w in W), 'bad format'
print('words:', len(W))
for pw in ['AA','BB','BC','CC','ABAB','ACBACA','CACBAC','ACACACB']:
    pat = ''.join(P[ch] for ch in pw)
    ev = sum(1 for w in W for o in range(0, 25-len(pat), 2) if w[o:o+len(pat)] == pat)
    print(f'{pw:8s} ({pat}) even-offset hits: {ev}')
# 10 pair
print('pair 10 even-offset hits:', sum(1 for w in W for o in range(0,24,2) if w[o:o+2]=='10'))
# check pair-sequence gaps between C's inside each 24-word (12 pairs)
gaps = set(); maxrun = 0
for w in W:
    ps = [w[o:o+2] for o in range(0,24,2)]
    cs = [i for i,p in enumerate(ps) if p=='11']
    gaps |= {b-a for a,b in zip(cs, cs[1:])}
    run = 0
    for p in ps:
        run = 0 if p=='11' else run+1
        maxrun = max(maxrun, run)
print('C-to-C gaps (in pairs) seen in 24-words:', sorted(gaps), ' max C-free run of pairs:', maxrun)
