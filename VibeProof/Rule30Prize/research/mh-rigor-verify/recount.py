import numpy as np
raw = np.fromfile("/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin", dtype=np.uint8)
bits = np.unpackbits(raw)
s = bits.tobytes()  # one byte per bit (0/1)
N = len(s)
for n in (19, 20, 21):
    # independent method: Python set of byte-slices on the first N positions (slow but different code path)
    if n == 20:
        b = bits.astype(np.uint64)
        L = N - n + 1
        w = np.zeros(L, dtype=np.uint64)
        for k in range(n):
            w = (w << np.uint64(1)) | b[k:k+L]
        u = np.unique(w)
        print("n=20 via np.unique:", u.size)
        allw = np.arange(1 << 20, dtype=np.uint64)
        missing = np.setdiff1d(allw, u)
        print("missing count:", missing.size)
        print("first few missing (as 20-bit words):", [format(int(x), "020b") for x in missing[:8]])
        # direct substring check on a byte string for the first missing word
        tgt = bytes(int(ch) for ch in format(int(missing[0]), "020b"))
        print("direct substring search for first missing word found:", s.find(tgt) != -1)
        tgt2 = bytes(int(ch) for ch in format(int(u[0]), "020b"))
        print("sanity: direct search for a present word found:", s.find(tgt2) != -1)
