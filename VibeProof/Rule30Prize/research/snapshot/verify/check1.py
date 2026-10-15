import hashlib, os, re, sys

SNAP = "/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize/lean"
CAT = "/Users/swish/src/wolfram/vibe-proof/ruliology-lean"
MANIFEST = "/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize/research/integrate-final/catalog_after.sha256"

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        h.update(f.read())
    return h.hexdigest()

def rd(p):
    with open(p, "rb") as f:
        return f.read()

problems = []

# 1. all .lean files under snapshot Ruliology/
snap_files = []
for root, dirs, files in os.walk(os.path.join(SNAP, "Ruliology")):
    for fn in files:
        rel = os.path.relpath(os.path.join(root, fn), SNAP)
        snap_files.append(rel)
snap_files.sort()
non_lean = [f for f in snap_files if not f.endswith(".lean")]
print("files under snapshot Ruliology/:", len(snap_files), "non-.lean:", non_lean)

# byte identity
for rel in snap_files:
    cp = os.path.join(CAT, rel)
    if not os.path.exists(cp):
        problems.append(f"no catalog file for {rel}")
        continue
    if rd(cp) != rd(os.path.join(SNAP, rel)):
        problems.append(f"DIFFERS from catalog: {rel}")
print("byte-identical check done")

# SHA256SUMS
sums = {}
with open(os.path.join(SNAP, "SHA256SUMS")) as f:
    for line in f:
        line = line.rstrip("\n")
        if not line.strip():
            continue
        m = re.fullmatch(r"([0-9a-f]{64})  (\S.*)", line)
        if not m:
            problems.append(f"bad SHA256SUMS line: {line!r}")
            continue
        if m.group(2) in sums:
            problems.append(f"duplicate entry {m.group(2)}")
        sums[m.group(2)] = m.group(1)
print("SHA256SUMS entries:", len(sums))
if set(sums) != set(snap_files):
    problems.append(f"SHA256SUMS set != snapshot files: missing={sorted(set(snap_files)-set(sums))} extra={sorted(set(sums)-set(snap_files))}")
for rel, h in sums.items():
    p = os.path.join(SNAP, rel)
    if not os.path.exists(p):
        problems.append(f"SHA256SUMS lists missing file {rel}")
        continue
    if sha(p) != h:
        problems.append(f"hash mismatch in SHA256SUMS for {rel}")
    cp = os.path.join(CAT, rel)
    if os.path.exists(cp) and sha(cp) != h:
        problems.append(f"catalog hash differs for {rel}")

# integration manifest
man = {}
with open(MANIFEST) as f:
    for line in f:
        line = line.rstrip("\n")
        if not line.strip():
            continue
        parts = line.split(None, 1)
        if len(parts) == 2:
            man[parts[1].strip()] = parts[0]
print("manifest entries:", len(man))
sample = list(man.keys())[:3]
print("manifest sample keys:", sample)
def man_lookup(rel):
    for k, v in man.items():
        if k == rel or k.endswith("/" + rel) or k.endswith(rel):
            return v
    return None
nomatch = []
for rel, h in sums.items():
    mh = man_lookup(rel)
    if mh is None:
        nomatch.append(rel)
    elif mh != h:
        problems.append(f"manifest hash differs for {rel}")
print("not found in manifest:", nomatch)

# import closure from the snapshot root, resolved against the CATALOG
def imports_of(path):
    out = []
    with open(path, encoding="utf-8") as f:
        txt = f.read()
    # Lean 4: imports must come at the beginning (after optional `module`/`prelude` and comments)
    # Strip block comments and line comments conservatively for the header region.
    # Collect all lines starting with 'import' anywhere, also 'public import' etc.
    for m in re.finditer(r"^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", txt, re.M):
        out.append(m.group(1))
    return out

def mod_to_rel(mod):
    return mod.replace(".", "/") + ".lean"

root_imports = imports_of(os.path.join(SNAP, "Ruliology.lean"))
seen = set()
stack = list(root_imports)
external = set()
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    rel = mod_to_rel(m)
    cp = os.path.join(CAT, rel)
    if not os.path.exists(cp):
        external.add(m)
        continue
    for i in imports_of(cp):
        stack.append(i)
closure_local = sorted(mod_to_rel(m) for m in seen if m not in external)
print("closure size (catalog-resolved):", len(closure_local))
print("external (non-catalog) imports:", sorted(external))
missing = sorted(set(closure_local) - set(snap_files))
extra = sorted(set(snap_files) - set(closure_local))
print("closure modules missing from snapshot:", missing)
print("snapshot files not in closure:", extra)
if missing:
    problems.append(f"missing closure modules: {missing}")

# Also, closure computed from the SNAPSHOT files themselves
seen2 = set(); stack = list(root_imports); ext2 = set()
while stack:
    m = stack.pop()
    if m in seen2: continue
    seen2.add(m)
    p = os.path.join(SNAP, mod_to_rel(m))
    if not os.path.exists(p):
        ext2.add(m); continue
    stack.extend(imports_of(p))
print("snapshot-resolved closure size:", len(seen2 - ext2), "unresolved:", sorted(ext2))

# counts
root_level = [f for f in snap_files if f.count("/") == 2]
certs = [f for f in snap_files if "/Rule30Certificates/" in f]
r30root = [f for f in root_level if os.path.basename(f).startswith("Rule30")]
print("root-level CellularAutomata files:", len(root_level), "Rule30* root-level:", len(r30root), "certs:", len(certs), "others:", [f for f in root_level if not os.path.basename(f).startswith("Rule30")])

print("PROBLEMS:", len(problems))
for p in problems:
    print("  ", p)
