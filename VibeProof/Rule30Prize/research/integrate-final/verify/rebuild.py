"""Check 2 driver: recompile new catalog modules one at a time, in the order given.

For each module M:
  * the transitive import closure is computed from the catalog sources and must equal the
    `importArts` keys of lake's setup JSON for M;
  * a fresh setup JSON is written under verify/setup with options {} and every NEW module's
    import redirected to the olean rebuilt here under verify/build (old modules keep the
    catalog's oleans, whose sources are unchanged);
  * `timeout 60 /usr/bin/time -l lake env lean <file> --setup <json> -o <verify olean>` runs
    from the catalog root (one Lean process at a time);
  * the rebuilt olean's SHA-256 is compared with the catalog's olean.
"""
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = "/Users/swish/src/wolfram/vibe-proof/ruliology-lean"
V = "/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/integrate-final/verify"
NEW = {l.strip()[:-5].replace("/", ".") for l in open(f"{V}/new_list.txt") if l.strip()}


def imports_of(mod):
    path = f"{ROOT}/{mod.replace('.', '/')}.lean"
    out = []
    for line in open(path, encoding="utf-8"):
        m = re.match(r"^import\s+(\S+)\s*$", line)
        if m:
            out.append(m.group(1))
    return out


def closure(mod):
    seen, stack = set(), list(imports_of(mod))
    while stack:
        m = stack.pop()
        if m in seen or not m.startswith("Ruliology"):
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


os.makedirs(f"{V}/logs", exist_ok=True)
fail = False
for mod in sys.argv[1:]:
    assert mod in NEW, f"{mod} is not a new module"
    rel = mod.replace(".", "/")
    src = f"{ROOT}/{rel}.lean"
    d = json.load(open(f"{ROOT}/.lake/build/ir/{rel}.setup.json"))
    problems = []
    if d.get("name") != mod:
        problems.append(f"setup name {d.get('name')}")
    for key in ("options", "plugins", "dynlibs"):
        if d.get(key) not in ({}, []):
            problems.append(f"catalog setup {key} = {d.get(key)}")
    cl = closure(mod)
    if set(d["importArts"]) != cl:
        problems.append(f"importArts != source closure: extra {set(d['importArts']) - cl}, missing {cl - set(d['importArts'])}")
    arts = {}
    for k in sorted(cl):
        if k in NEW:
            p = f"{V}/build/{k.replace('.', '/')}.olean"
            if not os.path.exists(p):
                problems.append(f"dependency {k} not rebuilt yet")
            arts[k] = [p]
        else:
            arts[k] = [f"{ROOT}/.lake/build/lib/lean/{k.replace('.', '/')}.olean"]
    my = {"plugins": [], "package": d.get("package"), "options": {}, "name": mod,
          "isModule": d.get("isModule", False), "importArts": arts, "dynlibs": []}
    sj = f"{V}/setup/{rel}.setup.json"
    os.makedirs(os.path.dirname(sj), exist_ok=True)
    json.dump(my, open(sj, "w"), indent=1)
    out = f"{V}/build/{rel}.olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    if os.path.exists(out):
        os.remove(out)
    if problems:
        print(f"{mod}: SETUP PROBLEMS {problems}")
        fail = True
        break
    cmd = ["timeout", "60", "/usr/bin/time", "-l", "lake", "env", "lean", src, "--setup", sj, "-o", out]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    log = f"{V}/logs/{mod}.log"
    with open(log, "w") as f:
        f.write(" ".join(cmd) + "\n--- stdout\n" + r.stdout + "\n--- stderr\n" + r.stderr)
    real = re.search(r"([\d.]+) real", r.stderr)
    rss = re.search(r"(\d+)\s+maximum resident set size", r.stderr)
    msgs = [l for l in r.stdout.splitlines() if re.search(r"error|sorry|warning", l)]
    cat_olean = f"{ROOT}/.lake/build/lib/lean/{rel}.olean"
    same = os.path.exists(out) and sha(out) == sha(cat_olean)
    print(f"{mod}: rc={r.returncode} real={real.group(1) if real else '?'}s "
          f"peak={int(rss.group(1)) / 1e9 if rss else 0:.2f}GB olean_identical={same} "
          f"msgs={len(msgs)}")
    for m in msgs[:8]:
        print("    ", m[:200])
    if r.returncode != 0 or not same:
        fail = True
        break
sys.exit(1 if fail else 0)
