import sys, re, os
root = sys.argv[1]
for fn in sorted(os.listdir(root)):
    if not fn.endswith('.lean'): continue
    src = open(os.path.join(root, fn), encoding='utf-8').read()
    # find top-level theorem/lemma declarations
    for m in re.finditer(r'^(theorem|lemma)\s+([^\s(:\[{]+)(.*?):=', src, re.S | re.M):
        stmt = (m.group(1) + ' ' + m.group(2) + m.group(3)).strip()
        stmt = re.sub(r'\s+', ' ', stmt)
        print(f"[{fn}] {stmt[:400]}")
