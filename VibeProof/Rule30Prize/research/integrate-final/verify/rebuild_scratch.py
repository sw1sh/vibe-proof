"""Rebuild the scratch (pre-integration) modules from their sources into verify/scratchbuild.

Module resolution:
  Ruliology            -> verify/oldroot/Ruliology.lean (the old 45-import root), olean in verify/scratchbuild
  Ruliology.*          -> catalog source; the catalog's prebuilt olean is used (old modules only)
  KC.*                 -> kernel-certify-r2/t1..t4/src
  P3*                  -> p3-ether/lean
Each module is compiled with `timeout 60 /usr/bin/time -l lake env lean <src> --setup <json> -o <out>`
(one Lean process at a time); the result is compared with the worker's original scratch olean.
"""
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = "/Users/swish/src/wolfram/vibe-proof/ruliology-lean"
R = "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize"
V = f"{R}/integrate-final/verify"
KCROOTS = [f"{R}/kernel-certify-r2/{t}/src" for t in ("t1", "t2", "t3", "t4")]
P3ROOT = f"{R}/p3-ether/lean"
OUT = f"{V}/scratchbuild"
NEW = {l.strip()[:-5].replace("/", ".") for l in open(f"{V}/new_list.txt") if l.strip()}


def src_of(mod):
    if mod == "Ruliology":
        return f"{V}/oldroot/Ruliology.lean"
    if mod.startswith("Ruliology."):
        return f"{ROOT}/{mod.replace('.', '/')}.lean"
    if mod.startswith("KC."):
        hits = [f"{r}/{mod.replace('.', '/')}.lean" for r in KCROOTS
                if os.path.exists(f"{r}/{mod.replace('.', '/')}.lean")]
        assert len(hits) == 1, (mod, hits)
        return hits[0]
    if mod.startswith("P3"):
        return f"{P3ROOT}/{mod}.lean"
    raise ValueError(mod)


def olean_of(mod):
    if mod.startswith("Ruliology."):
        assert mod not in NEW, f"scratch must not depend on new catalog module {mod}"
        return f"{ROOT}/.lake/build/lib/lean/{mod.replace('.', '/')}.olean"
    return f"{OUT}/{mod.replace('.', '/')}.olean"


def orig_olean(mod):
    if mod.startswith("KC."):
        for t in ("t1", "t2", "t3", "t4"):
            p = f"{R}/kernel-certify-r2/{t}/build/{mod.replace('.', '/')}.olean"
            if os.path.exists(p):
                return p
    if mod.startswith("P3"):
        return f"{P3ROOT}/build/{mod}.olean"
    return None


def imports_of(mod):
    out = []
    for line in open(src_of(mod), encoding="utf-8"):
        m = re.match(r"^import\s+(\S+)\s*$", line)
        if m:
            out.append(m.group(1))
    return out


def closure(mod):
    seen, stack = set(), list(imports_of(mod))
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(imports_of(m))
    return seen


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


fail = False
for mod in sys.argv[1:]:
    cl = closure(mod)
    arts = {}
    for k in sorted(cl):
        p = olean_of(k)
        if not os.path.exists(p):
            print(f"{mod}: dependency {k} has no olean at {p}")
            sys.exit(1)
        arts[k] = [p]
    setup = {"plugins": [], "package": None, "options": {}, "name": mod, "isModule": False,
             "importArts": arts, "dynlibs": []}
    sj = f"{V}/scratchsetup/{mod}.setup.json"
    os.makedirs(os.path.dirname(sj), exist_ok=True)
    json.dump(setup, open(sj, "w"), indent=1)
    out = olean_of(mod)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    if os.path.exists(out):
        os.remove(out)
    cmd = ["timeout", "60", "/usr/bin/time", "-l", "lake", "env", "lean", src_of(mod), "--setup", sj, "-o", out]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    with open(f"{V}/logs/scratch.{mod}.log", "w") as f:
        f.write(" ".join(cmd) + "\n--- stdout\n" + r.stdout + "\n--- stderr\n" + r.stderr)
    real = re.search(r"([\d.]+) real", r.stderr)
    rss = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
    errs = [l for l in r.stdout.splitlines() if re.search(r"error|sorry", l)]
    o = orig_olean(mod)
    ident = (sha(out) == sha(o)) if (o and os.path.exists(out) and os.path.exists(o)) else None
    print(f"{mod}: rc={r.returncode} real={real.group(1) if real else '?'}s "
          f"peak={int(rss.group(1)) / 1e9 if rss else 0:.2f}GB same_as_worker_olean={ident} errors={len(errs)}")
    for e in errs[:5]:
        print("    ", e[:200])
    if r.returncode != 0:
        fail = True
        break
sys.exit(1 if fail else 0)
