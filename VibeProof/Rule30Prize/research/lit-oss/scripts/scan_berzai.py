import sys, time
sys.path.insert(0, '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/lit-oss/scripts')
from berzai_kwindow import certify
from lyndon import lyndon_words
K = int(sys.argv[1]); n = int(sys.argv[2]); part = int(sys.argv[3]) if len(sys.argv) > 3 else 0; nparts = int(sys.argv[4]) if len(sys.argv) > 4 else 1
words = [''.join(map(str, w)) for w in lyndon_words(n)]
words = [w for i, w in enumerate(words) if i % nparts == part]
cert = []; t0 = time.time()
for w in words:
    ok, nv, info = certify([int(c) for c in w], K, max_states=5000)
    if ok: cert.append(w)
print(f"K={K} n={n} part={part}/{nparts}: tested={len(words)} certified={len(cert)} {cert} ({time.time()-t0:.1f}s)")
