# Summarize build logs: module, real seconds, peak RSS GB.
import glob, os, re, sys
R = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2'
for t in ['t1', 't2', 't3', 't4']:
    rows = []
    for fn in sorted(glob.glob(f'{R}/{t}/logs/KC.*.log')):
        txt = open(fn).read()
        m = re.search(r'([\d.]+) real', txt); mm = re.search(r'(\d+)\s+maximum resident set size', txt)
        err = 'error' in txt
        rows.append((os.path.basename(fn)[:-4], float(m.group(1)) if m else None, int(mm.group(1)) / 1e9 if mm else None, err))
    pre = sys.argv[1] if len(sys.argv) > 1 else ''
    for r in rows:
        if r[0].startswith(pre) or not pre:
            pass
    tot = {}
    for name, s, gb, err in rows:
        key = re.sub(r'\.C\d+$', '.C*', name)
        key = re.sub(r'(Certs|Cycles)\d+$', r'\1*', key)
        k = tot.setdefault(key, [0, 0.0, 0.0, 0])
        k[0] += 1; k[1] += s or 0; k[2] = max(k[2], gb or 0); k[3] += err
    for key, (n, s, gb, e) in sorted(tot.items()):
        print(f'{t}  {key:28s} files={n:3d} total={s:7.2f}s max_file={max(x[1] or 0 for x in rows if re.sub(r"\.C\d+$", ".C*", re.sub(r"(Certs|Cycles)\d+$", r"\1*", x[0])) == key):6.2f}s peakRSS={gb:.2f}GB errors={e}')
