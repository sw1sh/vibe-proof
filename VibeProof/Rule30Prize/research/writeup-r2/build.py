#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Assemble writeup-r2/rule30-state.html from registry.py, content.py and the outputs in this directory."""
import html, json, os, re, sys, glob, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import registry as REG
import content as C

HERE = os.path.dirname(os.path.abspath(__file__))
AX = os.path.join(HERE, 'ax')
R = REG.R

# ------------------------------------------------------------------ axioms
def parse_axioms(path):
    txt = open(path, encoding='utf-8').read()
    txt = re.sub(r'\n\s+', ' ', txt)
    out = {}
    for line in txt.split('\n'):
        m = re.match(r"'(.+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line)
        if m:
            out[m.group(1)] = [a.strip() for a in (m.group(3) or '').split(',') if a.strip()]
    return out

AXOUT = {os.path.basename(p): parse_axioms(p) for p in glob.glob(os.path.join(AX, '*.out'))}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

# ------------------------------------------------------------------ line numbers
_src_cache = {}
def find_line(path, name):
    if path not in _src_cache:
        _src_cache[path] = open(path, encoding='utf-8').read().split('\n')
    pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma)\s+' + re.escape(name) + r'(?=[\s:({\[]|$)')
    for i, line in enumerate(_src_cache[path]):
        if pat.match(line):
            return i + 1
    raise SystemExit(f'declaration {name} not found in {path}')

# ------------------------------------------------------------------ registry -> ids
ENTRY = {}
for i, e in enumerate(REG.T, 1):
    disp, absp, outf, prefix = REG.FILES[e['fid']]
    full = prefix + e['name']
    axs = AXOUT[outf].get(full)
    if axs is None:
        raise SystemExit(f'no axiom output for {full} in {outf}')
    if not set(axs) <= ALLOWED:
        raise SystemExit(f'disallowed axioms for {full}: {axs}')
    shortmod = {'JEN': 'Rule30Jen', 'PRIZE': 'Rule30Prize', 'DIAG': 'Rule30Diagonals', 'WIN': 'Rule30Window',
                'FW': 'Rule30FactorWindow', 'MJ': 'Rule30MaskedJen', 'BR': 'Rule30BlackRuns', 'BRB': 'Rule30BlackRunBlocks',
                'SC': 'Rule30StripCertificates', 'SCT': 'Rule30StripCertificateTable', 'WS': 'Rule30WhiteSeed',
                'DL': 'Rule30DrivenLeft', 'RP': 'Rule30RightPeriods', 'RZ': 'Rule30Realization', 'P2': 'Rule30PeriodTwo',
                'ZB': 'Rule30ZeroBoundary', 'ZBS': 'Rule30ZeroBoundaryStripe', 'P4S': 'Rule30PeriodFourSkeleton',
                'P2C': 'Rule30PeriodTwoCoupled'}
    shown = (shortmod[e['fid']] + '.' + e['name']) if e['fid'] in shortmod else full
    e.update(id=f'T{i}', full=full, shown=shown, axioms=axs, line=find_line(absp, e['name']), disp=disp, outf=outf)
    ENTRY[e['key']] = e

# ------------------------------------------------------------------ computations
COMP = [
 ('C1', 'D(W) ≤ 2W + 8 for every W ≤ 71 (largest first-violation time of a ZBL start of width ≤ W); equality only at W = 11.',
  'A-reconmap/c/zt2.c (W ≤ 71); progA-backdet/dfs.c → DW_table_phase0.txt (W ≤ 58); A-invsearch/maxdeath2.c → best_mode0.txt (W ≤ 40); A-monovariant/dfs.c (W ≤ 40, 50, 56, 58)',
  'zt2 re-run for all W ≤ 71 (writeup-r2/dw/zt2_*.txt, up to 64 parallel chunks); A-monovariant/dfs re-run; comparison writeup-r2/dw/combine.py → DW_table_writeup.txt; brute force writeup-r2/dw_brute.py for W ≤ 18',
  'Yes: four independent codes agree on every overlapping width (W ≤ 40 all four, W ≤ 58 at least two), and a fifth brute-force code agrees for W ≤ 18; W = 59–71 zt2 only. Lean covers W ≤ 16.'),
 ('C2', 'Stripe-prefix families S[1..m]·v·0^∞ die within 45 steps of the front’s arrival, for all m and all |v| ≤ 7.',
  'A-invsearch/front_cert.c (fc*.txt); A-monovariant/family.c; front_validate.py; family_validate.py',
  'family.c re-run for tails ≤ 4, 6, 7, 8; both validators re-run',
  'Yes: two independent certifiers agree; both validated against direct simulation.'),
 ('C3', 'Absorption into the ether-and-wall family (109-state Lean wall) for 0001, 0011, 0111: all 20,000 true right halves (T ≤ 5000, 4 phases) and all 262,144 prefix runs per word enter.',
  'B-edge-trap/entry2.c with wallmin_13.bin; writeup-r2/absorb/infamily_check.py; progB-avoid/check_surv.py',
  'All re-run (writeup-r2/absorb/); wallmin_13.bin checked equal to the Lean wallStates',
  'Yes: entry delays reproduced exactly by an independent implementation of InFamily on 9 cases.'),
 ('C4', 'Right half beside an alternating center: column 1 at white steps has only gaps 3 and 5 (blocks 100, 10000), density 3/14, bounded window discrepancy, fast-growing factor complexity.',
  'synth-r2/rc3.c, rc4.c, rc5.c, y_out.txt; writeup-r2/yindep.py, yanalyze.py, ytransient.py, blocklaw_strip.py',
  'rc3, rc4, rc5 re-run (y_out.txt reproduced byte for byte by rc5 2000 200000 0 0); yindep.py six runs; strip test b ≤ 12',
  'Yes for gaps and density (C and Python codes); factor counts to n = 64 by two codes; strip test single code.'),
 ('C5', 'Right-half law under alternation: column 1 is black at some white step among any 5 consecutive white steps (free bits have no 11111); forced by a width-4 strip.',
  'A-invsearch/rightstrip.c; writeup-r2/five_white.py',
  'Both re-run', 'Yes: two independent codes agree (widths 1–8); now also the Lean theorem Rule30ZeroBoundary.col1_black_among_five.'),
 ('C6', 'No nontrivial additive conservation law: rule 30 for r ≤ 10, rule 30² for r ≤ 8, alternating laws of rule 30² for r ≤ 9.',
  'A-invsearch/conslaw2.py (de Bruijn normal form, rank mod 2³¹−1); A-invsearch/conslaw_ring.py (all cyclic configurations); A-monovariant/conserved2.py (finite configurations, rank mod 2⁶¹−1)',
  'All re-run (writeup-r2/cons/)', 'Yes for r ≤ 5 (three methods) and r ≤ 8 ordinary (two methods); alternating r = 6–9 single method.'),
 ('C7', 'None of 15 natural quantities is monotone along surviving double steps (2,097,275 transitions, width ≤ 22).',
  'A-monovariant/mono.c', 'Re-run (writeup-r2/mono/mono_22.txt)', 'No.'),
 ('C8', 'No DFA with ≤ 5 states reading from the wall (or the edge) defines a ranking on 28 recorded surviving pairs.',
  'A-invsearch/dfa_rank_sat.py (CEGAR with z3); writeup-r2/dfa/dfa_recheck.py', 'UNSAT re-confirmed for n ≤ 5, both directions; n = 6 not re-confirmed within 60 s',
  'Partly: same encoding re-solved; the edge direction is superseded by the Lean theorem B6.'),
 ('C9', 'c7 is the ether shifted by 4 cells; the ether’s left half is a ZBL orbit satisfying the period-2 constraint with free bits 1010…, equal to the complements of column 1 at the white phases.',
  'synth-r2/ether_check.py', 'Re-run (writeup-r2/ether_check.out)', 'Now also proved in Lean (Rule30PeriodTwoCoupled.c7_eq_ether, ether_coupled_witness).'),
 ('C10', 'The progB-avoid relay configuration never enters S0001, and it enters the ether-and-wall family at t₁ = 159.',
  'progB-avoid/verify_relay.py; synth-r2/relay_family.py', 'Both re-run (writeup-r2/relay_family.out)', 'The two programs establish different, consistent facts; neither is duplicated.'),
 ('C11', 'Round-1 data facts: T + P ≥ 9,999,957 conditional on the external center-column data; ones balance and witness statistics to 10⁹ bits.',
  'Round-1 C programs on /Users/swish/src/wolfram/Ruliology/build/rule30/ (read-only data)', 'Not re-run in this pass', 'As recorded in BRIEF.md and BRIEF2.md.'),
 ('C12', 'Strip relaxations for 0001, 0011, 0111 have a bad strongly connected component at every width tried (b ≤ 22, 18, 18), growth 1.48–1.58 per step.',
  'progB-avoid/scc_an.c (an_*.txt, census.txt)', 'Not re-run', 'No.'),
 ('C13', 'C3(w) is not trivially false: for w = 0001, 0011, 0111, neither the empty start nor any start with leftmost black cell at depth ≤ 14 keeps the pattern P_w on [150, 300).',
  'writeup-r2/c3_zero.py', 'Written and run in this pass', 'No.'),
]
COMPIDS = {c[0] for c in COMP}

# ------------------------------------------------------------------ placeholders
def esc(s):
    return html.escape(s, quote=False)

def wbr(s, chars='._/'):
    """escape and allow line breaks after the given characters (for long Lean names and paths)."""
    out = esc(s)
    for ch in chars:
        out = out.replace(ch, ch + '<wbr>')
    return out

def mini(s):
    """escape plain text and turn `code` into <code>."""
    out = esc(s)
    return re.sub(r'`([^`]+)`', r'<code>\1</code>', out)

CHIP = {'ok': ('ok', 'proved'), 'kernel': ('ok', 'proved'), 'impl': ('impl', 'implication'), 'paper': ('paper', 'paper'),
        'comp': ('comp', 'computed'), 'open': ('open', 'open'), 'ref': ('ref', 'refuted'), 'third': ('third', 'third-party')}

def fill(s):
    def tref(m):
        kind, key = m.group(1), m.group(2)
        if kind == 'C':
            if key not in COMPIDS:
                raise SystemExit('unknown computation ' + key)
            return f'<a class="cref" href="#{key}">{key}</a>'
        e = ENTRY.get(key)
        if e is None:
            raise SystemExit('unknown theorem key ' + key)
        if kind == 'T':
            return f'<a class="tref" href="#{e["id"]}" title="{esc(e["shown"])}">{e["id"]}</a>'
        return f'<a class="nref" href="#{e["id"]}" title="{e["id"]}"><code>{wbr(e["shown"])}</code></a>'
    s = re.sub(r'\[\[([TNC]):([A-Za-z0-9_]+)\]\]', tref, s)
    def chip(m):
        cls, label = CHIP[m.group(1)]
        return f'<span class="chip {cls}">{label}</span>'
    s = re.sub(r'\{\{chip:([a-z]+)\}\}', chip, s)
    return s

# ------------------------------------------------------------------ D(W) data
def load_dw():
    zt = collections.defaultdict(list)
    for fn in glob.glob(os.path.join(HERE, 'dw', 'zt2_a*_n*_c*.txt')):
        a, n, c = map(int, re.search(r'zt2_a(\d+)_n(\d+)_c(\d+)\.txt', fn).groups())
        t = open(fn).read()
        m = re.search(r'deepest surviving depth=(\d+) => all die by depth', t)
        if not m or 'TIMEOUT' in t:
            raise SystemExit('bad zt2 output ' + fn)
        zt[a].append((n, c, int(m.group(1))))
    D = {}
    for a, lst in zt.items():
        n = lst[0][0]
        assert sorted(c for _, c, _ in lst) == list(range(n))
        D[a - 1] = max(d for _, _, d in lst)
    pa = {int(W): int(d) for W, d in re.findall(r'W=(\d+) best death time=(\d+)', open(R + 'progA-backdet/DW_table_phase0.txt').read())}
    inv = {int(W): int(d) for W, d in re.findall(r'mode=0 W=(\d+) maxdeath=(\d+)', open(R + 'A-invsearch/best_mode0.txt').read())}
    mono = {int(W): int(d) for W, d in re.findall(r'W=\s*(\d+)\s+maxprefix=\s*(\d+)', open(os.path.join(HERE, 'dw', 'mono_dfs_1_40.txt')).read())}
    mono.update({50: 92, 56: 100, 58: 110})
    return D, pa, inv, mono

DW, PA, INV, MONO = load_dw()
assert sorted(DW) == list(range(1, 72))
for tab in (PA, INV, MONO):
    for W, d in tab.items():
        assert DW[W] == d, (W, d, DW[W])
assert all(DW[W] <= 2 * W + 8 for W in DW)
assert [W for W in DW if DW[W] == 2 * W + 8] == [11]

def dw_chart():
    W0, W1, Y0, Y1 = 0, 72, 0, 160
    x0, x1, yt, yb = 56, 676, 22, 282
    X = lambda w: x0 + (w - W0) / (W1 - W0) * (x1 - x0)
    Y = lambda d: yb - (d - Y0) / (Y1 - Y0) * (yb - yt)
    parts = []
    parts.append(f'<svg class="dwchart" viewBox="0 0 780 330" role="img" aria-labelledby="dwtitle dwdesc">')
    parts.append('<title id="dwtitle">D(W) against the bound 2W + 8</title>')
    parts.append('<desc id="dwdesc">Step line of the largest first-violation time D(W) for widths 1 to 71, below the straight line 2W + 8 everywhere, touching it only at W = 11.</desc>')
    for d in range(0, 161, 40):
        parts.append(f'<line class="grid" x1="{x0}" x2="{x1}" y1="{Y(d):.1f}" y2="{Y(d):.1f}"/>')
        parts.append(f'<text class="tick" x="{x0 - 8}" y="{Y(d) + 4:.1f}" text-anchor="end">{d}</text>')
    for w in range(0, 71, 10):
        parts.append(f'<line class="grid faint" x1="{X(w):.1f}" x2="{X(w):.1f}" y1="{yt}" y2="{yb}"/>')
        parts.append(f'<text class="tick" x="{X(w):.1f}" y="{yb + 18}" text-anchor="middle">{w}</text>')
    parts.append(f'<text class="axlabel" x="{(x0 + x1) / 2:.1f}" y="{yb + 40}" text-anchor="middle">support width W</text>')
    parts.append(f'<text class="axlabel" x="{x0}" y="{yt - 8}" text-anchor="start">time</text>')
    # bound line
    parts.append(f'<line class="bound" x1="{X(1):.1f}" y1="{Y(10):.1f}" x2="{X(71):.1f}" y2="{Y(150):.1f}"/>')
    parts.append(f'<text class="lbl" x="{X(71) + 8:.1f}" y="{Y(150) + 4:.1f}">2W + 8</text>')
    # step line
    pts = []
    for w in range(1, 72):
        if w == 1:
            pts.append(f'M{X(1):.1f},{Y(DW[1]):.1f}')
        else:
            pts.append(f'H{X(w):.1f}V{Y(DW[w]):.1f}')
    parts.append(f'<path class="dwline" d="{"".join(pts)}"/>')
    parts.append(f'<circle class="dot" cx="{X(11):.1f}" cy="{Y(30):.1f}" r="4.5"/>')
    parts.append(f'<text class="lbl" x="{X(11) + 10:.1f}" y="{Y(30) + 22:.1f}">W = 11: D = 30 = 2W + 8</text>')
    parts.append(f'<circle class="dot" cx="{X(71):.1f}" cy="{Y(DW[71]):.1f}" r="4.5"/>')
    parts.append(f'<text class="lbl" x="{X(71) + 8:.1f}" y="{Y(DW[71]) + 4:.1f}">D(71) = {DW[71]}</text>')
    parts.append(f'<line id="dwcross" class="cross" x1="0" x2="0" y1="{yt}" y2="{yb}" visibility="hidden"/>')
    parts.append(f'<rect id="dwhit" class="hit" x="{x0}" y="{yt}" width="{x1 - x0}" height="{yb - yt}"/>')
    parts.append('</svg>')
    meta = dict(x0=x0, x1=x1, W0=W0, W1=W1, D={str(k): v for k, v in DW.items()})
    return '\n'.join(parts), meta

def dw_table():
    rows = []
    for W in range(1, 72):
        codes = 1 + (W in PA) + (W in INV) + (W in MONO)
        rows.append(f'<tr><td>{W}</td><td>{DW[W]}</td><td>{2 * W + 8}</td><td>{2 * W + 8 - DW[W]}</td><td>{codes}</td></tr>')
    return ('<details class="tableview"><summary>Table view: D(W) for W = 1..71</summary><div class="tframe"><table class="numtab compact">'
            '<thead><tr><th>W</th><th>D(W)</th><th>2W + 8</th><th>slack</th><th>agreeing codes</th></tr></thead><tbody>'
            + ''.join(rows) + '</tbody></table></div></details>')

# ------------------------------------------------------------------ theorem index
def theorem_index():
    secname = dict(REG.SECTIONS)
    out = ['<div class="tframe tall"><table class="thmtab" id="thmtab"><colgroup><col class="c-id"><col class="c-name"><col class="c-stmt"><col class="c-stat"><col class="c-ax"></colgroup><thead><tr><th>ID</th><th>Lean name and source</th>'
           '<th>Statement</th><th>Status</th><th>Axioms</th></tr></thead>']
    cur = None
    for e in REG.T:
        if e['sec'] != cur:
            if cur is not None:
                out.append('</tbody>')
            cur = e['sec']
            out.append(f'<tbody class="grp"><tr class="grouprow"><th colspan="5" scope="colgroup"><a href="#{cur}">{esc(secname[cur])}</a></th></tr>')
        if e['kind'] == 'impl':
            status = f'<span class="chip impl">implication</span><span class="hyp">hypothesis: <code>{esc(e["hyp"])}</code></span>'
        elif e['kind'] == 'kernel':
            status = '<span class="chip ok">proved</span><span class="hyp">kernel computation</span>'
        else:
            status = '<span class="chip ok">proved</span>'
        axs = ', '.join(e['axioms']) if e['axioms'] else 'none'
        out.append(f'<tr id="{e["id"]}"><td class="tid">{e["id"]}</td><td class="tname"><code>{wbr(e["shown"])}</code>'
                   f'<span class="loc">{wbr(e["disp"], "/")}:{e["line"]}</span></td>'
                   f'<td class="tstmt">{mini(e["stmt"])}</td><td class="tstat">{status}</td><td class="tax">{esc(axs)}</td></tr>')
    out.append('</tbody></table></div>')
    return '\n'.join(out)

def comp_index():
    out = ['<div class="tframe"><table class="comptab"><colgroup><col class="k-id"><col class="k-fact"><col class="k-prog"><col class="k-run"><col></colgroup>'
           '<thead><tr><th>ID</th><th>Fact</th><th>Programs</th><th>This pass</th><th>Cross-validated</th></tr></thead><tbody>']
    for cid, fact, progs, rerun, xval in COMP:
        out.append(f'<tr id="{cid}"><td class="tid">{cid}</td><td>{wbr(fact, "_")}</td><td class="prog">{wbr(progs, "/_")}</td>'
                   f'<td>{wbr(rerun, "/_")}</td><td>{wbr(xval, "._/")}</td></tr>')
    out.append('</tbody></table></div>')
    return '\n'.join(out)

def axiom_audit():
    rows = []
    srcmap = [('ax_r1.out', 'All 11 staged round-1 modules plus Rule30Jen, Rule30Prize, Rule30Diagonals, Rule30Window, via <code>import Ruliology</code> (<code>lake env lean</code>)'),
              ('ax_r1_staged.out', 'The same 142 theorems against the staged oleans in <code>curation/build</code> (LEAN_PATH); output identical'),
              ('chk_ZBLCore.out', 'progA-backdet/lean/ZBLCore.lean'), ('chk_ZBLmono.out', 'A-monovariant/lean/ZBL.lean'),
              ('chk_Supp.out', 'V-A2-epochs-rigor/Supp.lean'), ('chk_ZBLrecon.out', 'A-reconmap/lean/ZBL.lean'),
              ('chk_ZBLcheck.out', 'verify-A2-reconmap-rigor/ZBLcheck.lean'), ('chk_A1Reform.out', 'verify-A1reform-rigor/A1Reform.lean'),
              ('chk_ZBLBarrier.out', 'A-invsearch/lean/ZBLBarrier.lean'), ('chk_Corollary.out', 'verify-A2-rigor/ZBLBarrierCorollary.lean'),
              ('chk_JointBarrier.out', 'A-invsearch/lean/JointBarrier.lean'), ('chk_EdgeDFA.out', 'A-invsearch/lean/ZBLEdgeDFA.lean'),
              ('chk_EtherWall.out', 'B-edge-trap/lean/EtherWall.lean'), ('chk_Skel0001.out', 'progB-avoid/lean/Skel0001.lean'),
              ('chk_Skel0011.out', 'progB-avoid/lean/Skel0011.lean'), ('chk_DirectSkel0011.out', 'verify-b2-rigor/DirectSkel0011.lean'),
              ('ax_r2_staged.out', 'All theorems of the seven staged integration modules, compiled from source into <code>writeup-r2/build</code> in this pass')]
    total = 0
    for outf, src in srcmap:
        d = AXOUT[outf]
        bad = [k for k, v in d.items() if not set(v) <= ALLOWED]
        total += len(d)
        rc = ''
        rcf = os.path.join(AX, outf.replace('.out', '.rc'))
        if os.path.exists(rcf):
            rc = esc(open(rcf).read().strip().split(' ', 1)[1])
        rows.append(f'<tr><td>{src}</td><td class="num">{len(d)}</td><td>{"none" if not bad else esc(", ".join(bad))}</td>'
                    f'<td>{rc or "&lt; 1 s"}</td><td><code>writeup-r2/ax/{outf}</code></td></tr>')
    used = len(REG.T)
    import hashlib
    bt = {}
    btf = os.path.join(AX, 'build_times.txt')
    if os.path.exists(btf):
        for line in open(btf):
            m = re.match(r'(\S+) rc=(\d+) (\d+)s', line.strip())
            if m and m.group(2) == '0':
                bt[m.group(1)] = m.group(3)
    hrows = []
    for mod in ['Rule30ZeroBoundary', 'Rule30ZeroBoundaryStripe', 'Rule30ZeroBoundarySmall', 'Rule30ZeroBoundaryBarriers',
                'Rule30Ether', 'Rule30PeriodFourSkeleton', 'Rule30PeriodTwoCoupled']:
        src = REG.STG + mod + '.lean'
        h = hashlib.sha256(open(src, 'rb').read()).hexdigest()[:16]
        nth = sum(1 for k in AXOUT['ax_r2_staged.out'] if k.startswith('Ruliology.CellularAutomata.' + mod + '.'))
        hrows.append(f'<tr><td><code>{mod}</code></td><td class="num">{nth}</td><td>{bt.get(mod, "?")} s</td><td><code>{h}</code></td></tr>')
    htable = ('<p>The seven staged integration modules were checked at these versions (sha256 prefixes); a later edit of a '
              'staged file is not covered by this audit.</p><div class="tframe"><table class="numtab"><thead><tr><th>Module</th>'
              '<th>theorems</th><th>build</th><th>sha256 prefix</th></tr></thead><tbody>' + ''.join(hrows) + '</tbody></table></div>')
    return (f'<p>{used} theorems are cited in this report and every one of them appears in these outputs; {total} distinct '
            'name–file pairs were printed in all. No output lists an axiom other than <code>propext</code>, <code>Classical.choice</code> '
            'or <code>Quot.sound</code>; in particular no <code>sorryAx</code> and no <code>Lean.ofReduceBool</code> (native_decide). '
            'A text scan of every source file found no <code>sorry</code>, <code>admit</code>, <code>native_decide</code> or '
            '<code>axiom</code> declaration. Round-2 files were checked as byte-identical copies with <code>#print axioms</code> lines '
            'appended (<code>writeup-r2/ax/chk_*.lean</code>), compiled with <code>timeout 60 lake env lean</code> from '
            '<code>ruliology-lean</code>.</p>'
            '<div class="tframe"><table class="numtab"><thead><tr><th>Source</th><th>theorems</th><th>disallowed</th><th>compile</th><th>output</th></tr></thead><tbody>'
            + ''.join(rows) + '</tbody></table></div>' + htable)

# ------------------------------------------------------------------ page
CSS = r"""
:root {
  /* Layout: one reading column (about 72ch) beside a sticky contents rail on wide screens; wide tables and code scroll in their own frames. */
  --bg: #F4F5F2; --surface: #FFFFFF; --ink: #16191C; --ink-2: #3C4249; --muted: #616A73; --rule: #D5D9D1; --rule-2: #BFC5BB;
  --accent: #0B6A68; --accent-wash: #DDEEEB; --cell-on: #1E2226; --cell-off: #FFFFFF; --cell-hi: #0B6A68; --cell-hi-off: #CFE7E3;
  --ok: #2B7631; --ok-wash: #E0EFE0; --impl: #855400; --impl-wash: #F5E8CE; --paper: #62449A; --paper-wash: #EAE3F5;
  --comp: #2A5793; --comp-wash: #DFE8F5; --open: #A9271E; --open-wash: #F6DEDB; --ref: #5B6066; --ref-wash: #E6E7E8;
  --third: #74552A; --third-wash: #F0E7DA; --code-bg: #EEF0EB;
  --font-body: "Charter", "Bitstream Charter", "Iowan Old Style", "Palatino Linotype", Palatino, "Book Antiqua", Georgia, serif;
  --font-head: "Avenir Next", Avenir, "Segoe UI", "Helvetica Neue", system-ui, -apple-system, sans-serif;
  --font-mono: ui-monospace, "SF Mono", SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #111416; --surface: #181C1F; --ink: #E6E9EB; --ink-2: #C3C9CE; --muted: #959EA7; --rule: #2B3135; --rule-2: #3B4247;
    --accent: #5EC3BB; --accent-wash: #15302E; --cell-on: #DCE1E4; --cell-off: #181C1F; --cell-hi: #5EC3BB; --cell-hi-off: #1B3533;
    --ok: #7FCB83; --ok-wash: #1A2E1C; --impl: #E4B65E; --impl-wash: #382B12; --paper: #BCA4EC; --paper-wash: #2A2340;
    --comp: #91B7EE; --comp-wash: #1A2940; --open: #F2918A; --open-wash: #3A1E1C; --ref: #ABB0B6; --ref-wash: #2A2D31;
    --third: #D8B78D; --third-wash: #32281C; --code-bg: #1F2427; color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --bg: #111416; --surface: #181C1F; --ink: #E6E9EB; --ink-2: #C3C9CE; --muted: #959EA7; --rule: #2B3135; --rule-2: #3B4247;
  --accent: #5EC3BB; --accent-wash: #15302E; --cell-on: #DCE1E4; --cell-off: #181C1F; --cell-hi: #5EC3BB; --cell-hi-off: #1B3533;
  --ok: #7FCB83; --ok-wash: #1A2E1C; --impl: #E4B65E; --impl-wash: #382B12; --paper: #BCA4EC; --paper-wash: #2A2340;
  --comp: #91B7EE; --comp-wash: #1A2940; --open: #F2918A; --open-wash: #3A1E1C; --ref: #ABB0B6; --ref-wash: #2A2D31;
  --third: #D8B78D; --third-wash: #32281C; --code-bg: #1F2427; color-scheme: dark;
}
* { box-sizing: border-box; }
html { -webkit-text-size-adjust: 100%; }
body { margin: 0; background: var(--bg); color: var(--ink); font-family: var(--font-body); font-size: 17px; line-height: 1.6; }
.page { max-width: 1240px; margin: 0 auto; padding-left: max(16px, env(safe-area-inset-left, 0px)); padding-right: max(16px, env(safe-area-inset-right, 0px)); padding-block: 28px 64px; }
a { color: var(--accent); text-decoration-thickness: 1px; text-underline-offset: 2px; }
a:focus-visible, input:focus-visible, summary:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
code, pre { font-family: var(--font-mono); font-size: 0.84em; }
code { background: var(--code-bg); padding: 0.05em 0.3em; border-radius: 3px; overflow-wrap: break-word; }
pre code { background: none; padding: 0; overflow-wrap: normal; }
h1, h2, h3, .eyebrow, .chip, th, .lbl, .tick, .axlabel, figcaption, .meta, .toc { font-family: var(--font-head); }
h1 { font-size: clamp(1.7rem, 1.2rem + 2.2vw, 2.6rem); line-height: 1.15; margin: 0 0 10px; letter-spacing: -0.01em; text-wrap: balance; font-weight: 650; }
h2 { font-size: 1.45rem; line-height: 1.25; margin: 0 0 14px; padding-top: 10px; text-wrap: balance; font-weight: 650; display: flex; gap: 12px; align-items: baseline; }
h3 { font-size: 1.08rem; margin: 28px 0 8px; text-wrap: balance; font-weight: 650; }
.secno { color: var(--accent); font-variant-numeric: tabular-nums; min-width: 1.4em; }
p, ul, ol { margin: 0 0 12px; }
ul, ol { padding-left: 1.3em; }
li { margin-bottom: 6px; }
sub, sup { line-height: 0; }
header.top { display: grid; grid-template-columns: minmax(0, 1fr) auto; gap: 28px; align-items: end; padding-bottom: 22px; border-bottom: 1px solid var(--rule); margin-bottom: 26px; }
.eyebrow { text-transform: uppercase; letter-spacing: 0.12em; font-size: 0.74rem; color: var(--muted); margin-bottom: 8px; }
.meta { color: var(--muted); font-size: 0.9rem; margin: 6px 0 0; }
.seedwrap { text-align: right; }
#seedCanvas { width: 380px; max-width: 100%; height: auto; image-rendering: pixelated; display: block; }
.seedcap { font-family: var(--font-head); font-size: 0.75rem; color: var(--muted); margin-top: 6px; max-width: 380px; text-align: left; }
.layout { display: grid; grid-template-columns: 230px minmax(0, 1fr); gap: 40px; align-items: start; }
.toc { position: sticky; top: calc(env(safe-area-inset-top, 0px) + 16px); font-size: 0.86rem; line-height: 1.45; max-height: calc(100vh - 32px); overflow-y: auto; padding-right: 4px; }
.toc ol { list-style: none; padding: 0; margin: 0; display: grid; gap: 2px; }
.toc a { display: block; padding: 4px 8px; border-radius: 4px; color: var(--ink-2); text-decoration: none; }
.toc a:hover { background: var(--accent-wash); color: var(--ink); }
.toc .sub a { padding-left: 22px; font-size: 0.8rem; color: var(--muted); }
.toc .tlabel { text-transform: uppercase; letter-spacing: 0.1em; font-size: 0.7rem; color: var(--muted); margin: 0 0 6px 8px; }
main { min-width: 0; }
main > section, main > .abstract, main > .legend, main > .glance-wrap { margin-bottom: 40px; }
section { scroll-margin-top: 12px; }
h3[id] { scroll-margin-top: 12px; }
.prose-width p, .prose-width ul, .prose-width ol { max-width: 74ch; }
.abstract { background: var(--surface); border: 1px solid var(--rule); border-radius: 6px; padding: 18px 22px; max-width: 80ch; }
.abstract h2 { font-size: 1rem; text-transform: uppercase; letter-spacing: 0.1em; color: var(--muted); padding: 0; margin-bottom: 8px; }
.abstract p { margin: 0; }
.lead { color: var(--ink-2); }
.legend { display: flex; flex-wrap: wrap; gap: 10px 18px; font-size: 0.86rem; color: var(--ink-2); font-family: var(--font-head); max-width: 100%; }
.legend span.item { display: inline-flex; gap: 6px; align-items: baseline; }
.chip { display: inline-block; font-size: 0.7rem; font-weight: 600; letter-spacing: 0.05em; text-transform: uppercase; padding: 1px 7px; border-radius: 999px; border: 1px solid currentColor; white-space: nowrap; vertical-align: 1px; line-height: 1.5; }
.chip.ok { color: var(--ok); background: var(--ok-wash); }
.chip.impl { color: var(--impl); background: var(--impl-wash); }
.chip.paper { color: var(--paper); background: var(--paper-wash); }
.chip.comp { color: var(--comp); background: var(--comp-wash); }
.chip.open { color: var(--open); background: var(--open-wash); }
.chip.ref { color: var(--ref); background: var(--ref-wash); }
.chip.third { color: var(--third); background: var(--third-wash); }
.glance { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 300px), 1fr)); gap: 12px; }
.g-item { background: var(--surface); border: 1px solid var(--rule); border-radius: 6px; padding: 12px 14px; display: grid; gap: 6px; align-content: start; min-width: 0; }
.g-item p { margin: 0; font-size: 0.95rem; line-height: 1.5; }
.g-item .chip { justify-self: start; }
.stmt { background: var(--surface); border: 1px solid var(--rule-2); border-left-width: 1px; border-radius: 6px; padding: 12px 16px; margin: 14px 0; max-width: 84ch; min-width: 0; }
.stmt-h { font-family: var(--font-head); font-weight: 650; margin-bottom: 6px; display: flex; gap: 10px; align-items: center; flex-wrap: wrap; }
.stmt pre { margin: 8px 0 4px; overflow-x: auto; }
.stmt p { margin: 0 0 6px; }
.codeframe { background: var(--surface); border: 1px solid var(--rule); border-radius: 6px; padding: 12px 16px; overflow-x: auto; max-width: 84ch; margin-bottom: 12px; }
.codeframe pre { margin: 0; }
.tframe { overflow-x: auto; margin: 12px 0 16px; border: 1px solid var(--rule); border-radius: 6px; background: var(--surface); max-width: 100%; }
.tframe.tall { max-height: 80vh; overflow-y: auto; }
table { border-collapse: collapse; width: 100%; font-size: 0.9rem; line-height: 1.45; }
th, td { text-align: left; vertical-align: top; padding: 7px 10px; border-bottom: 1px solid var(--rule); }
thead th { font-size: 0.76rem; text-transform: uppercase; letter-spacing: 0.06em; color: var(--muted); font-weight: 600; background: var(--surface); position: sticky; top: 0; z-index: 1; }
tbody tr:last-child td { border-bottom: none; }
.deftab td:first-child { font-family: var(--font-head); font-weight: 600; white-space: nowrap; }
.deftab.narrow { width: auto; }
.numtab td, .numtab th { font-variant-numeric: tabular-nums; }
.numtab.compact td { padding: 3px 10px; }
td.num { text-align: right; font-variant-numeric: tabular-nums; }
.thmtab { min-width: 840px; table-layout: fixed; }
.thmtab col.c-id { width: 52px; } .thmtab col.c-name { width: 29%; } .thmtab col.c-stmt { width: 37%; } .thmtab col.c-stat { width: 118px; } .thmtab col.c-ax { width: 136px; }
.thmtab .loc { display: block; font-family: var(--font-mono); font-size: 0.7rem; color: var(--muted); margin-top: 3px; line-height: 1.35; }
.thmtab .tid, .comptab .tid { font-family: var(--font-head); font-weight: 600; white-space: nowrap; font-variant-numeric: tabular-nums; }
.thmtab .tname code { background: none; padding: 0; font-size: 0.8rem; }

.thmtab .tax { font-family: var(--font-mono); font-size: 0.7rem; color: var(--ink-2); line-height: 1.35; }


.hyp { display: block; font-size: 0.72rem; color: var(--muted); margin-top: 3px; white-space: normal; font-family: var(--font-head); }
.hyp code { font-size: 0.95em; }
.grouprow th { background: var(--accent-wash); color: var(--ink); font-size: 0.82rem; text-transform: none; letter-spacing: 0; position: static; }
.grouprow a { color: inherit; text-decoration: none; }
tr:target td { background: var(--accent-wash); }
.comptab { min-width: 860px; table-layout: fixed; }
.comptab col.k-id { width: 48px; } .comptab col.k-fact { width: 30%; } .comptab col.k-prog { width: 26%; } .comptab col.k-run { width: 20%; }
.comptab .prog { font-family: var(--font-mono); font-size: 0.76rem; }
.littab { min-width: 860px; table-layout: fixed; }
.littab col.l-work { width: 17%; } .littab col.l-claim { width: 33%; } .littab col.l-rel { width: 34%; } .littab col.l-stat { width: 16%; }
.littab td .chip { white-space: normal; }
.tref, .cref { font-family: var(--font-head); font-size: 0.86em; font-weight: 600; text-decoration: none; padding: 0 3px; border-radius: 3px; background: var(--accent-wash); white-space: nowrap; }
.nref { text-decoration: none; }
.nref code { color: var(--accent); }
.wordlist { font-family: var(--font-mono); font-size: 0.82em; overflow-wrap: anywhere; }
.filterbar { display: flex; flex-wrap: wrap; gap: 10px 16px; align-items: center; margin: 8px 0; font-family: var(--font-head); font-size: 0.9rem; }
.filterbar input { font: inherit; padding: 6px 10px; border: 1px solid var(--rule-2); border-radius: 5px; background: var(--surface); color: var(--ink); min-width: 0; width: min(100%, 360px); }
.filterbar .count { color: var(--muted); font-variant-numeric: tabular-nums; }
figure.fig { margin: 16px 0; display: grid; gap: 8px; justify-items: start; }
figure.fig canvas { max-width: 100%; height: auto; image-rendering: pixelated; border: 1px solid var(--rule); border-radius: 4px; }
figcaption { font-size: 0.84rem; color: var(--muted); max-width: 70ch; line-height: 1.45; }
.chartwrap { position: relative; background: var(--surface); border: 1px solid var(--rule); border-radius: 6px; padding: 10px 6px 4px; margin: 12px 0; overflow-x: auto; }
.dwchart { width: 100%; min-width: 560px; height: auto; display: block; }
.dwchart .grid { stroke: var(--rule); stroke-width: 1; }
.dwchart .grid.faint { stroke: var(--rule); opacity: 0.6; }
.dwchart .tick { fill: var(--muted); font-size: 12px; font-variant-numeric: tabular-nums; }
.dwchart .axlabel { fill: var(--ink-2); font-size: 12.5px; }
.dwchart .lbl { fill: var(--ink-2); font-size: 12.5px; }
.dwchart .bound { stroke: var(--muted); stroke-width: 1.5; }
.dwchart .dwline { stroke: var(--accent); stroke-width: 2; fill: none; stroke-linejoin: round; stroke-linecap: round; }
.dwchart .dot { fill: var(--accent); stroke: var(--surface); stroke-width: 2; }
.dwchart .cross { stroke: var(--ink-2); stroke-width: 1; }
.dwchart .hit { fill: transparent; cursor: crosshair; }
.chartkey { display: flex; flex-wrap: wrap; gap: 6px 18px; font-family: var(--font-head); font-size: 0.82rem; color: var(--ink-2); padding: 2px 10px 6px; }
.chartkey .k { display: inline-flex; gap: 6px; align-items: center; }
.chartkey .sw { display: inline-block; width: 18px; height: 0; border-top: 2px solid var(--accent); }
.chartkey .sw.b { border-top: 1.5px solid var(--muted); }
.tip { position: absolute; pointer-events: none; background: var(--surface); color: var(--ink); border: 1px solid var(--rule-2); border-radius: 5px; padding: 5px 9px; font-family: var(--font-head); font-size: 0.8rem; line-height: 1.4; font-variant-numeric: tabular-nums; box-shadow: 0 2px 8px rgba(0,0,0,0.12); white-space: nowrap; }
details.tableview { margin: 8px 0 16px; }
details.tableview summary { cursor: pointer; font-family: var(--font-head); font-size: 0.9rem; color: var(--accent); }
details.tableview .tframe { max-height: 420px; overflow-y: auto; }
footer { border-top: 1px solid var(--rule); margin-top: 40px; padding-top: 14px; color: var(--muted); font-size: 0.85rem; font-family: var(--font-head); }
@media (max-width: 980px) {
  .layout { grid-template-columns: minmax(0, 1fr); gap: 18px; }
  .toc { position: static; max-height: none; border: 1px solid var(--rule); border-radius: 6px; padding: 10px; background: var(--surface); }
  .toc ol { grid-template-columns: repeat(auto-fit, minmax(min(100%, 220px), 1fr)); }
  .toc .sub { display: none; }
}
@media (max-width: 720px) {
  body { font-size: 16px; }
  header.top { grid-template-columns: minmax(0, 1fr); }
  .seedwrap { text-align: left; }
  .deftab td:first-child { white-space: normal; }
}
@media (prefers-reduced-motion: reduce) { * { scroll-behavior: auto !important; } }
"""

JS = r"""
(function () {
  function tok(n) { return getComputedStyle(document.documentElement).getPropertyValue(n).trim(); }
  function drawSeed() {
    var cv = document.getElementById('seedCanvas'); if (!cv || !cv.getContext) return;
    var rows = 48, half = 47, cs = 4, w = (2 * half + 1) * cs, h = rows * cs;
    cv.width = w; cv.height = h;
    var g = cv.getContext('2d'), on = tok('--cell-on'), off = tok('--cell-off'), hi = tok('--cell-hi'), hio = tok('--cell-hi-off');
    g.fillStyle = off; g.fillRect(0, 0, w, h);
    var row = new Array(2 * half + 3).fill(0); row[half + 1] = 1;
    for (var t = 0; t < rows; t++) {
      for (var p = 0; p < 2 * half + 1; p++) {
        var v = row[p + 1], center = (p === half);
        g.fillStyle = center ? (v ? hi : hio) : (v ? on : off);
        if (v || center) g.fillRect(p * cs, t * cs, cs, cs);
      }
      var nx = new Array(row.length).fill(0);
      for (var q = 1; q < row.length - 1; q++) nx[q] = row[q - 1] ^ (row[q] | row[q + 1]);
      row = nx;
    }
  }
  function drawEther() {
    var cv = document.getElementById('etherCanvas'); if (!cv || !cv.getContext) return;
    var n = 21, steps = 12, cs = 20; cv.width = n * cs; cv.height = steps * cs;
    var g = cv.getContext('2d'), on = tok('--cell-on'), off = tok('--cell-off'), hi = tok('--cell-hi'), hio = tok('--cell-hi-off'), grid = tok('--rule');
    var row = []; for (var i = 0; i < n; i++) { var p = i - 10; row.push(((p + 1) % 7 + 7) % 7 === 0 ? 1 : 0); }
    for (var t = 0; t < steps; t++) {
      for (var i2 = 0; i2 < n; i2++) {
        var p2 = i2 - 10, v = row[i2], center = (((p2 % 7) + 7) % 7 === 0);
        g.fillStyle = center ? (v ? hi : hio) : (v ? on : off);
        g.fillRect(i2 * cs, t * cs, cs, cs);
      }
      var nx = []; for (var j = 0; j < n; j++) nx.push(row[(j - 1 + n) % n] ^ (row[j] | row[(j + 1) % n]));
      row = nx;
    }
    g.strokeStyle = grid; g.lineWidth = 1;
    for (var x = 0; x <= n; x++) { g.beginPath(); g.moveTo(x * cs + 0.5, 0); g.lineTo(x * cs + 0.5, steps * cs); g.stroke(); }
    for (var y = 0; y <= steps; y++) { g.beginPath(); g.moveTo(0, y * cs + 0.5); g.lineTo(n * cs, y * cs + 0.5); g.stroke(); }
  }
  function drawAll() { try { drawSeed(); drawEther(); } catch (e) {} }
  drawAll();
  try { window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', drawAll); } catch (e) {}
  try { new MutationObserver(drawAll).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] }); } catch (e) {}

  var inp = document.getElementById('tfilter'), cnt = document.getElementById('tcount'), tab = document.getElementById('thmtab');
  if (inp && tab) {
    var rows = Array.prototype.slice.call(tab.querySelectorAll('tbody tr[id]'));
    var groups = Array.prototype.slice.call(tab.querySelectorAll('tbody.grp'));
    var update = function () {
      var q = inp.value.trim().toLowerCase(), shown = 0;
      rows.forEach(function (r) { var ok = !q || r.textContent.toLowerCase().indexOf(q) >= 0; r.hidden = !ok; if (ok) shown++; });
      groups.forEach(function (gb) { var any = gb.querySelector('tr[id]:not([hidden])'); var head = gb.querySelector('.grouprow'); if (head) head.hidden = !any; });
      if (cnt) cnt.textContent = shown + ' of ' + rows.length + ' shown';
    };
    inp.addEventListener('input', update); update();
  }

  var meta = window.DWMETA, svg = document.querySelector('.dwchart'), hit = document.getElementById('dwhit'), cross = document.getElementById('dwcross'), tip = document.getElementById('dwtip');
  if (meta && svg && hit && cross && tip) {
    var wrap = svg.parentNode;
    var move = function (ev) {
      var pt = svg.createSVGPoint(); pt.x = ev.clientX; pt.y = ev.clientY;
      var m = svg.getScreenCTM(); if (!m) return; var loc = pt.matrixTransform(m.inverse());
      var W = Math.round(meta.W0 + (loc.x - meta.x0) / (meta.x1 - meta.x0) * (meta.W1 - meta.W0));
      if (W < 1) W = 1; if (W > 71) W = 71;
      var x = meta.x0 + (W - meta.W0) / (meta.W1 - meta.W0) * (meta.x1 - meta.x0);
      cross.setAttribute('x1', x); cross.setAttribute('x2', x); cross.setAttribute('visibility', 'visible');
      var D = meta.D[String(W)], B = 2 * W + 8;
      tip.textContent = 'W = ' + W + '   D(W) = ' + D + '   2W + 8 = ' + B + '   slack ' + (B - D);
      tip.hidden = false;
      var r = wrap.getBoundingClientRect(), left = ev.clientX - r.left + wrap.scrollLeft + 14, top = ev.clientY - r.top - 34;
      if (left + tip.offsetWidth > wrap.scrollWidth - 4) left = ev.clientX - r.left + wrap.scrollLeft - tip.offsetWidth - 14;
      tip.style.left = left + 'px'; tip.style.top = Math.max(4, top) + 'px';
    };
    hit.addEventListener('pointermove', move);
    hit.addEventListener('pointerleave', function () { tip.hidden = true; cross.setAttribute('visibility', 'hidden'); });
  }
})();
"""

def toc():
    items = [
        ('s1', '1 Problem 1 and definitions', []),
        ('s2', '2 Unconditional results', [('s2-jen', 'Jen, constant columns'), ('s2-diag', 'Diagonal periods'), ('s2-win', 'Windows'),
                                          ('s2-mj', 'Masked Jen'), ('s2-br', 'Black runs'), ('s2-sc', 'Strip certificates'), ('s2-ws', 'White seed')]),
        ('s3', '3 Reductions', [('s3-p2', 'Period 2'), ('s3-p4', 'Absorption'), ('s3-c3', 'C3(w)')]),
        ('s4', '4 Structural theorems', [('s4-real', 'Realization, conjugacy'), ('s4-clock', 'Jen with a clock'), ('s4-epoch', 'Epochs'),
                                        ('s4-stripe', 'Stripes'), ('s4-small', 'Width checks'), ('s4-ether', 'Ether and wall'),
                                        ('s4-skel', 'Skeletons'), ('s4-dl', 'Driven left half'), ('s4-rp', 'Right diagonals')]),
        ('s5', '5 Barriers', [('s5-q01', 'Q01-only'), ('s5-joint', 'JointBarrier'), ('s5-edge', 'Edge region'), ('s5-cons', 'Conservation laws')]),
        ('s6', '6 Computations', [('s6-dw', 'D(W) ≤ 2W + 8'), ('s6-stripe', 'Stripe prefixes'), ('s6-absorb', 'Absorption'), ('s6-block', 'Block law, 3/14')]),
        ('s7', '7 Refuted claims', []),
        ('s8', '8 Prior and third-party work', []),
        ('s9', '9 Frontier and assessment', []),
        ('theorems', 'A Theorem index', []),
        ('computations', 'B Computation index', []),
        ('audit', 'C Axiom audit', []),
    ]
    out = ['<nav class="toc" aria-label="Contents"><p class="tlabel">Contents</p><ol>']
    for href, label, subs in items:
        out.append(f'<li><a href="#{href}">{esc(label)}</a></li>')
        for sh, sl in subs:
            out.append(f'<li class="sub"><a href="#{sh}">{esc(sl)}</a></li>')
    out.append('</ol></nav>')
    return '\n'.join(out)

def build():
    chart_svg, meta = dw_chart()
    legend = ('<div class="legend" aria-label="Status labels">'
              '<span class="item"><span class="chip ok">proved</span> Lean, axioms re-printed here</span>'
              '<span class="item"><span class="chip impl">implication</span> Lean theorem with an open hypothesis</span>'
              '<span class="item"><span class="chip paper">paper</span> argument from Lean lemmas, not formalized</span>'
              '<span class="item"><span class="chip comp">computed</span> finite computation, program named</span>'
              '<span class="item"><span class="chip open">open</span></span>'
              '<span class="item"><span class="chip ref">refuted</span></span>'
              '<span class="item"><span class="chip third">third-party</span> not verified unless stated</span></div>')
    s6 = (C.S6_HEAD + C.S6_DW_TEXT +
          '<div class="chartwrap">' + chart_svg + '<div class="tip" id="dwtip" hidden></div>'
          '<div class="chartkey"><span class="k"><span class="sw"></span>D(W), widths 1–71</span>'
          '<span class="k"><span class="sw b"></span>bound 2W + 8</span></div></div>' + dw_table() + C.S6_DW_AFTER + C.S6_REST)
    nthm = len(REG.T)
    N2 = len(AXOUT['ax_r2_staged.out'])
    nimpl = sum(1 for e in REG.T if e['kind'] == 'impl')
    nkern = sum(1 for e in REG.T if e['kind'] == 'kernel')
    body = f"""<div class="page">
<header class="top">
  <div>
    <p class="eyebrow">Rule 30 Prize · Problem 1 · state of the attack</p>
    <h1>Rule 30 Problem 1: where the attack stands after rounds 1 and 2</h1>
    <p class="meta">15 October 2026 · for the project and collaborators · {nthm} Lean theorems cited, each with its axioms re-printed in this pass · {len(COMP)} computations indexed</p>
  </div>
  <div class="seedwrap"><canvas id="seedCanvas" width="380" height="192" aria-label="The first 48 rows of rule 30 from a single black cell, with the center column highlighted"></canvas>
  <p class="seedcap">Rows 0–47 from one black cell. The highlighted column is c(t), the subject of Problem 1.</p></div>
</header>
<div class="layout">
{toc()}
<main class="prose-width">
<div class="abstract"><h2>Abstract</h2><p>{esc(' '.join(C.ABSTRACT.split()))}</p></div>
{legend}
<div class="glance-wrap">{fill(C.GLANCE)}</div>
{fill(C.S1)}
{fill(C.S2)}
{fill(C.S3)}
{fill(C.S4)}
{fill(C.S5)}
{fill(s6)}
{fill(C.S7)}
{fill(C.S8)}
{fill(C.S9)}
<section id="theorems">
<h2><span class="secno">A</span> Theorem index</h2>
<p>Every Lean declaration cited above, in section order: {nthm} entries, of which {nkern} rest on a kernel-checked finite
computation and {nimpl} are implications from an open hypothesis. Paths are relative to
<code>/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/</code>, except <code>ruliology-lean/…</code>, which is under
<code>/Users/swish/src/wolfram/vibe-proof/</code>. The eleven round-1 <code>staging/</code> modules are byte-identical to the copies already
integrated in <code>ruliology-lean/Ruliology/CellularAutomata/</code>. After round 2 the integration task staged seven
deduplicated modules (<code>Rule30ZeroBoundary</code>, <code>…Stripe</code>, <code>…Small</code>, <code>…Barriers</code>,
<code>Rule30Ether</code>, <code>Rule30PeriodFourSkeleton</code>, <code>Rule30PeriodTwoCoupled</code>) that re-prove the round-2
results in one encoding and add the glue theorems; this index cites the round-2 originals plus the glue theorems,
and §C lists the check of all {N2} theorems of the seven modules.</p>
<div class="filterbar"><label for="tfilter">Filter</label><input id="tfilter" type="search" placeholder="name, file or words, e.g. golden, ZBLCore, absorption" autocomplete="off"><span class="count" id="tcount" aria-live="polite"></span></div>
{theorem_index()}
</section>
<section id="computations">
<h2><span class="secno">B</span> Computation index</h2>
<p>Each computational fact used in the report, the programs behind it, what was re-run in this pass (every run under a
60-second limit) and whether an independent code agrees. Nothing here is a proof.</p>
{comp_index()}
</section>
<section id="audit">
<h2><span class="secno">C</span> Axiom audit</h2>
{axiom_audit()}
</section>
</main>
</div>
<footer>Generated by <code>writeup-r2/build.py</code> from the round-1 and round-2 sources and the checks stored in
<code>writeup-r2/</code>. Third-party material was read as text only.</footer>
</div>"""
    page = ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
            '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
            '<meta name="claude:viewport-fit-sides" content="cover">\n'
            '<title>Rule 30 Problem 1</title>\n'
            '<style>' + CSS + '</style>\n</head>\n<body>\n' + body +
            '\n<script>window.DWMETA = ' + json.dumps(meta) + ';</script>\n<script>' + JS + '</script>\n</body>\n</html>\n')
    # sanity: no unresolved placeholders
    left = re.findall(r'\[\[[^\]]*\]\]|\{\{[^}]*\}\}', page)
    if left:
        raise SystemExit('unresolved placeholders: ' + repr(left[:5]))
    out = os.path.join(HERE, 'rule30-state.html')
    open(out, 'w', encoding='utf-8').write(page)
    print('wrote', out, len(page), 'bytes;', nthm, 'theorems;', len(COMP), 'computations')

if __name__ == '__main__':
    build()
