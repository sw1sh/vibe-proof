#!/usr/bin/env python3
"""Generate the final-batch Rule 30 catalog modules from the scratch sources.

Only names change in Lean code: namespaces (KC.* -> Ruliology.CellularAutomata.Rule30*), imports,
and the regrouping of the 256 width-52 chunk theorems (16 files -> 4 modules, sub-namespaces C0..C15
kept). Docstrings are rewritten (scratch module names replaced, provenance added).
Every replacement is checked to occur exactly the expected number of times.
usage: python3 -I gen_catalog.py OUT_ROOT [PER_MODULE]
"""
import os
import re
import sys

J = '/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize'
T1 = f'{J}/kernel-certify-r2/t1/src/KC'
T2 = f'{J}/kernel-certify-r2/t2/src/KC'
T3 = f'{J}/kernel-certify-r2/t3/src/KC'
T4 = f'{J}/kernel-certify-r2/t4/src/KC'
P3 = f'{J}/p3-ether/lean'

OUT = sys.argv[1]
PER = int(sys.argv[2]) if len(sys.argv) > 2 else 4  # chunk files (of 16 chunks) per data module
CA = os.path.join(OUT, 'Ruliology', 'CellularAutomata')
CERT = os.path.join(CA, 'Rule30Certificates')
os.makedirs(CERT, exist_ok=True)

written = []


def read(p):
    with open(p, encoding='utf-8') as f:
        return f.read()


def rep(text, old, new, count=1):
    n = text.count(old)
    if n != count:
        raise SystemExit(f'replacement count {n} != {count} for:\n{old!r}')
    return text.replace(old, new)


def write(rel, text):
    p = os.path.join(CA, rel)
    with open(p, 'w', encoding='utf-8') as f:
        f.write(text)
    written.append(p)


def kc_sources(target, extra=''):
    return ('Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): kernel certification,\n'
            f'round 2 (`kernel-certify-r2`, target {target}){extra}; adversarially verified.')


P3_SOURCES = ('Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): period-3 study\n'
              '(`p3-ether`); adversarially verified.')

# ---------------------------------------------------------------------------------------------
# t1: Q01Lanes -> Rule30ZeroBoundaryLanes
s = read(f'{T1}/Q01Lanes.lean')
s = rep(s, "  depths `≤ W` has a white cell at depth `1` at some even time `< K`.\n-/\n",
        "  depths `≤ W` has a white cell at depth `1` at some even time `< K`.\n"
        "* `q01_of_chunks`: the same from a combined range certificate `ChunksOK`.\n"
        "\n"
        "`Rule30ZeroBoundaryWidth52` runs the checker at width `52`: all `256` chunks pass with `97` levels.\n"
        "\n" + kc_sources(1, ', bit-sliced `Q01` checker') + "\n-/\n")
s = rep(s, "namespace KC\nnamespace Q01Lanes\n\nopen Ruliology.CellularAutomata Rule30ZeroBoundary\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30ZeroBoundaryLanes\n\nopen Rule30ZeroBoundary\n")
s = rep(s, "end Q01Lanes\nend KC\n", "end Rule30ZeroBoundaryLanes\nend Ruliology.CellularAutomata\n")
write('Rule30ZeroBoundaryLanes.lean', s)

# t1: the 16 chunk files C0..C15 -> 16 / PER data modules
NFILES = 16
WORDS = {1: 'one', 2: 'two', 4: 'four', 8: 'eight'}
assert NFILES % PER == 0
NMOD = NFILES // PER
chunk_doc = {}
chunk_body = {}
for j in range(NFILES):
    c = read(f'{T1}/Q01W52/C{j}.lean')
    m = re.fullmatch(r"import KC\.Q01Lanes\n\n(/-! [^\n]* -/)\n\nnamespace KC\.Q01W52\.C(\d+)\nopen KC\.Q01Lanes\n\n"
                     r"(.*)\n\nend KC\.Q01W52\.C(\d+)\n", c, re.S)
    assert m and int(m.group(2)) == j and int(m.group(4)) == j, j
    chunk_doc[j] = m.group(1)
    chunk_body[j] = m.group(3)
    lo = 16 * j
    for c_ in range(lo, lo + 16):
        assert f'theorem c{c_} : check 52 97 18 {c_} = true := by decide +kernel\n' in chunk_body[j], c_
    assert chunk_body[j].count('by decide +kernel') == 16
    assert f'theorem range : ChunksOK 52 97 18 {lo} 16 :=' in chunk_body[j]

for k in range(NMOD):
    js = list(range(k * PER, (k + 1) * PER))
    lo, hi = 16 * js[0], 16 * js[-1] + 15
    parts = [
        "import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes\n\n"
        "/-!\n"
        f"# `Q01` at width `52`: the chunk checks `{lo}` to `{hi}`\n\n"
        "Data for `Rule30ZeroBoundaryWidth52`: the kernel checks `check 52 97 18 c = true`\n"
        "(`Rule30ZeroBoundaryLanes.check`, `decide +kernel`) for the chunks "
        f"`c = {lo}, …, {hi}` of `256`\n"
        "(`2 ^ 18` lanes each, `97` levels). They sit in the namespaces "
        f"`Rule30ZeroBoundaryWidth52.C{js[0]}` –\n"
        f"`C{js[-1]}`, `16` chunks each; each of these namespaces combines its chunks into\n"
        "`range : ChunksOK 52 97 18 lo 16`.\n\n"
        + kc_sources(1, '; the `16` generated chunk files (`gen.py`)\n'
                        f'are regrouped here, {WORDS[PER]} to a module') + "\n-/\n\n"
        "namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52\n\n"
        "open Rule30ZeroBoundaryLanes\n"
    ]
    for j in js:
        parts.append(f"\n{chunk_doc[j]}\n\nnamespace C{j}\n\n{chunk_body[j]}\n\nend C{j}\n")
    parts.append("\nend Ruliology.CellularAutomata.Rule30ZeroBoundaryWidth52\n")
    write(f'Rule30Certificates/ZeroBoundaryWidth52Chunks{k}.lean', ''.join(parts))

# t1: Q01W52 -> Rule30ZeroBoundaryWidth52
s = read(f'{T1}/Q01W52.lean')
s = rep(s, ''.join(f'import KC.Q01W52.C{j}\n' for j in range(16)),
        ''.join(f'import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryWidth52Chunks{k}\n'
                for k in range(NMOD)))
s = rep(s, "depth `1` (column `-1`) at some even time `≤ 96`. The 256 chunk checks are in\n"
           "`KC.Q01W52.C0` – `KC.Q01W52.C15`; soundness is `KC.Q01Lanes.q01_of_chunks`.\n-/\n",
        "depth `1` (column `-1`) at some even time `≤ 96`. The 256 chunk checks are in the namespaces\n"
        "`Rule30ZeroBoundaryWidth52.C0` – `C15`, in the modules\n"
        f"`Rule30Certificates.ZeroBoundaryWidth52Chunks0` – `ZeroBoundaryWidth52Chunks{NMOD - 1}` "
        f"({16 * PER} chunks each);\n"
        "soundness is `Rule30ZeroBoundaryLanes.q01_of_chunks`.\n"
        "\n"
        "* `q01_width_le_52`: the bound `96`, which is `D(52)` of the round-2 death-time table (its\n"
        "  tightness is observed, not proved).\n"
        "* `q01_width_le_52_linear`: the bound `2 W + 8`.\n"
        "* `not_inX_of_width_le_52`: `Q01` restricted to widths `≤ 52` (`¬ Rule30ZeroBoundary.InX x`).\n"
        "\n"
        "`W ≤ 56` was also kernel-checked (`KC.Q01W56.q01_width_le_56`, bound `100`; `1024` chunks in `64`\n"
        "files, about `345` s of kernel time). It lives, with its build script (`build.sh`,\n"
        "`buildall56.sh`; set their `B` to that directory), in\n"
        "`/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize/research/kernel-certify-r2/t1`.\n"
        "It is not in the catalog because of build cost.\n"
        "\n" + kc_sources(1) + "\n-/\n")
s = rep(s, "namespace KC.Q01W52\nopen KC.Q01Lanes Ruliology.CellularAutomata Rule30ZeroBoundary\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30ZeroBoundaryWidth52\n\n"
        "open Rule30ZeroBoundaryLanes Rule30ZeroBoundary\n")
s = rep(s, "end KC.Q01W52\n", "end Rule30ZeroBoundaryWidth52\nend Ruliology.CellularAutomata\n")
write('Rule30ZeroBoundaryWidth52.lean', s)

# ---------------------------------------------------------------------------------------------
# t2: StripeFront -> Rule30ZeroBoundaryStripeFront
s = read(f'{T2}/StripeFront.lean')
s = rep(s, "finite certificate (the orbit length `lam` and checkpoints along the orbit) covers every arrival\n"
           "time `d - 1` at once (`front_sound`).\n-/\n",
        "finite certificate (the orbit length `lam` and checkpoints along the orbit) covers every arrival\n"
        "time `d - 1` at once (`front_sound`).\n"
        "\n"
        "* `stripe_below`, `win_step`, `win_orb`: the window evolves on its own up to the arrival time.\n"
        "* `seg`, `seg_sound`, `PathOK`, `Cycle`, `orb_mod`: checked orbit segments and periodic orbits.\n"
        "* `sig_sound`, `front_sound`: a checked cycle bounds the death time of every such start.\n"
        "* `row3`, `devB`, `family_of_class`: the family `S[1..m] · b₀ b₁ b₂ · 0^∞` reduces to its class\n"
        "  data; `Rule30ZeroBoundaryStripeFamily` finishes it with the cycles of\n"
        "  `Rule30Certificates.ZeroBoundaryStripeCycles0` – `ZeroBoundaryStripeCycles2`.\n"
        "\n" + kc_sources(2, ', stripe-prefix family') + "\n-/\n")
s = rep(s, "namespace KC\nnamespace StripeFront\n\nopen Ruliology.CellularAutomata Rule30ZeroBoundary Rule30ZeroBoundarySmall\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30ZeroBoundaryStripeFront\n\n"
        "open Rule30ZeroBoundary Rule30ZeroBoundarySmall\n")
s = rep(s, "end StripeFront\nend KC\n", "end Rule30ZeroBoundaryStripeFront\nend Ruliology.CellularAutomata\n")
write('Rule30ZeroBoundaryStripeFront.lean', s)

# t2: StripeCycles0..2 -> Rule30Certificates/ZeroBoundaryStripeCycles0..2
cyc_desc = {
    0: ("six cycles of length `4096` or `16384`",
        "`cyc_0_1`, `cyc_1_0`, `cyc_6_1` (length `4096`) and `cyc_2_1`, `cyc_3_0`, `cyc_7_0` (length\n"
        "`16384`), one `seg` check each."),
    1: ("the cycle `cyc_4_1`, length `65536`",
        "`cyc_4_1` (length `65536`), in four `seg` checks of `16384` steps."),
    2: ("the cycle `cyc_5_0`, length `65536`",
        "`cyc_5_0` (length `65536`), in four `seg` checks of `16384` steps."),
}
for k in range(3):
    s = read(f'{T2}/StripeCycles{k}.lean')
    title, lst = cyc_desc[k]
    s = rep(s, "import KC.StripeFront\n", "import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront\n")
    s = rep(s, "/-! Kernel-checked front-window cycles (window `32`, post-arrival horizon `31`). -/\n",
            "/-!\n"
            f"# The stripe-prefix family: front-window cycles ({title})\n\n"
            "Data for `Rule30ZeroBoundaryStripeFamily`: kernel-checked front-window cycles (window `32`,\n"
            "post-arrival horizon `31`), as `Rule30ZeroBoundaryStripeFront.Cycle` certificates whose\n"
            "segments are checked by `seg` with `decide +kernel` and joined by `seg_sound` and `path_append`:\n"
            f"{lst}\n\n" + kc_sources(2) + "\n-/\n")
    s = rep(s, f"namespace KC.StripeFront.StripeCycles{k}\nopen KC.StripeFront\n",
            f"namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles{k}\n\n"
            "open Rule30ZeroBoundaryStripeFront\n")
    s = rep(s, f"end KC.StripeFront.StripeCycles{k}\n",
            f"end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles{k}\n")
    write(f'Rule30Certificates/ZeroBoundaryStripeCycles{k}.lean', s)

# t2: StripeFamily -> Rule30ZeroBoundaryStripeFamily (namespace Rule30ZeroBoundaryStripeFront)
s = read(f'{T2}/StripeFamily.lean')
s = rep(s, "import KC.StripeCycles0\nimport KC.StripeCycles1\nimport KC.StripeCycles2\n",
        "import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles0\n"
        "import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles1\n"
        "import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles2\n")
s = rep(s, "`≤ d - 1 + 31`. The proof is `family_of_class` (front window, `KC.StripeFront`) with one of eight\n"
           "kernel-checked periodic window orbits per class `(m mod 2, v)`.\n-/\n",
        "`≤ d - 1 + 31`. The proof is `family_of_class` (front window, `Rule30ZeroBoundaryStripeFront`) with\n"
        "one of eight kernel-checked periodic window orbits per class `(m mod 2, v)`\n"
        "(`Rule30Certificates.ZeroBoundaryStripeCycles0` – `ZeroBoundaryStripeCycles2`). The theorems live\n"
        "in the namespace `Rule30ZeroBoundaryStripeFront`.\n"
        "\n"
        "* `stripe_prefix_family`: the word given as three Booleans.\n"
        "* `stripe_prefix_family_list`: the word given as a list `v` with `|v| ≤ 3` (`rowV`).\n"
        "\n"
        "Only tails `|v| ≤ 3` are kernel-checked; the bound `31` after arrival is attained (computation).\n"
        "\n" + kc_sources(2) + "\n-/\n")
s = rep(s, "namespace KC.StripeFront\nopen KC.StripeFront.StripeCycles0\nopen KC.StripeFront.StripeCycles1\n"
           "open KC.StripeFront.StripeCycles2\nopen Ruliology.CellularAutomata Rule30ZeroBoundary\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30ZeroBoundaryStripeFront\n\n"
        "open Rule30ZeroBoundaryStripeFront.StripeCycles0\nopen Rule30ZeroBoundaryStripeFront.StripeCycles1\n"
        "open Rule30ZeroBoundaryStripeFront.StripeCycles2\nopen Rule30ZeroBoundary\n")
s = rep(s, "end KC.StripeFront\n", "end Rule30ZeroBoundaryStripeFront\nend Ruliology.CellularAutomata\n")
write('Rule30ZeroBoundaryStripeFamily.lean', s)

# ---------------------------------------------------------------------------------------------
# t3: EtherTrap -> Rule30EtherTrap
s = read(f'{T3}/EtherTrap.lean')
s = rep(s, "* `KC.EtherTrapCerts`: kernel checks of the round-2 certificates (`B-edge-trap/cert_*_20.txt`)\n"
           "  for every pure-ether node of width `20` of `0001`, `0011`, `0111`.\n"
           "* `escapes_of_width_20`, `proj_*`: a closed set of width `b ≤ 20` lifts to width `20`.\n-/\n",
        "* `Rule30Certificates.EtherTrap0` – `EtherTrap5`: kernel checks of the round-2 certificates\n"
        "  (`B-edge-trap/cert_*_20.txt`) for every pure-ether node of width `20` of `0001`, `0011`, `0111`;\n"
        "  `Rule30EtherTrapWidth20` combines them.\n"
        "* `stepW_take`, `escapes_take`: a closed set of width `b ≤ 20` lifts to width `20`.\n"
        "* `node_succ`, `node_traj`: the driven right half (`Rule30Ether.node`) is a path of the\n"
        "  relaxation along column `b + 1`, so the trap notion here is the one masked Jen uses.\n"
        "\n" + kc_sources(3, ', ether traps') + "\n-/\n")
s = rep(s, "namespace KC\nnamespace EtherTrap\n\nopen Ruliology.CellularAutomata Rule30Ether Rule30StripCertificates\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30EtherTrap\n\nopen Rule30Ether Rule30StripCertificates\n")
s = rep(s, "end EtherTrap\nend KC\n", "end Rule30EtherTrap\nend Ruliology.CellularAutomata\n")
write('Rule30EtherTrap.lean', s)

# t3: EtherTrapCerts0..5 -> Rule30Certificates/EtherTrap0..5
for k in range(6):
    s = read(f'{T3}/EtherTrapCerts{k}.lean')
    m = re.search(r"/-! Kernel-checked certificates for `(\d{4})` \(data: `B-edge-trap/cert_(\d{4})_20\.txt`, "
                  r"converted to\ncolumn-`21` inputs\): from each pure-ether node of width `20`, a path to a node "
                  r"with two closed walks of\nequal length whose white-phase outputs differ\. -/\n", s)
    assert m and m.group(1) == m.group(2), k
    word = m.group(1)
    names = re.findall(r'^theorem (cert_\d{4}_\d+_\d) :', s, re.M)
    assert len(names) == 4 and all(n.startswith(f'cert_{word}_') for n in names), (k, names)
    assert s.count('by decide +kernel') == 4
    j0 = names[0].split('_')[2]
    assert all(n.split('_')[2] == j0 for n in names)
    s = s.replace(m.group(0),
                  "/-!\n"
                  f"# Pure ether, word `{word}`: certificates for the alignment `j₀ = {j0}`\n\n"
                  f"Data for `Rule30EtherTrapWidth20`: kernel-checked certificates for `{word}` (data:\n"
                  f"`B-edge-trap/cert_{word}_20.txt`, converted to column-`21` inputs): from each pure-ether "
                  "node of\n"
                  "width `20`, a path to a node with two closed walks of equal length whose white-phase outputs\n"
                  f"differ (`certOK`, `decide +kernel`): `{names[0]}` – `{names[-1]}` (phases `0` – `3`).\n\n"
                  + kc_sources(3) + "\n-/\n", 1)
    s = rep(s, "import KC.EtherTrap\n", "import Ruliology.CellularAutomata.Rule30EtherTrap\n")
    s = rep(s, "namespace KC.EtherTrap\nopen Ruliology.CellularAutomata Rule30Ether\n",
            "namespace Ruliology.CellularAutomata.Rule30EtherTrap\n\nopen Rule30Ether\n")
    s = rep(s, "end KC.EtherTrap\n", "end Ruliology.CellularAutomata.Rule30EtherTrap\n")
    write(f'Rule30Certificates/EtherTrap{k}.lean', s)

# t3: EtherTrapMain -> Rule30EtherTrapWidth20 (namespace Rule30EtherTrap)
s = read(f'{T3}/EtherTrapMain.lean')
s = rep(s, ''.join(f'import KC.EtherTrapCerts{k}\n' for k in range(6)),
        ''.join(f'import Ruliology.CellularAutomata.Rule30Certificates.EtherTrap{k}\n' for k in range(6)))
s = rep(s, "eventually periodic (`pure_ether_escapes_*`). Hence no trap of width `≤ 20` contains the pure-ether\n"
           "node (`pure_ether_not_in_trap_*`).\n-/\n",
        "eventually periodic (`pure_ether_escapes_*`). Hence no trap of width `≤ 20` contains the pure-ether\n"
        "node (`pure_ether_not_in_trap_*`). The theorems live in the namespace `Rule30EtherTrap`; the\n"
        "`24` certificates are in `Rule30Certificates.EtherTrap0` – `EtherTrap5`.\n"
        "\n"
        "This concerns the strip relaxation, where column `b + 1` is arbitrary. It says nothing about\n"
        "whether the true right half reaches the pure ether, and absorption remains open.\n"
        "\n" + kc_sources(3) + "\n-/\n")
s = rep(s, "namespace KC.EtherTrap\nopen Ruliology.CellularAutomata Rule30Ether Rule30StripCertificates\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30EtherTrap\n\nopen Rule30Ether Rule30StripCertificates\n")
s = rep(s, "end KC.EtherTrap\n", "end Rule30EtherTrap\nend Ruliology.CellularAutomata\n")
write('Rule30EtherTrapWidth20.lean', s)

# ---------------------------------------------------------------------------------------------
# t4: PeriodTwoLang -> Rule30PeriodTwoLanguage
s = read(f'{T4}/PeriodTwoLang.lean')
s = rep(s, "white phases (subset simulation over bitmasks of strips, `simMask`). `no_pattern` combines the two:\n"
           "eventually, column `1` at the white times never spells `pat`.\n-/\n",
        "white phases (subset simulation over bitmasks of strips, `simMask`). `no_pattern` combines the two:\n"
        "eventually, column `1` at the white times never spells `pat`.\n"
        "\n"
        "`Rule30PeriodTwoWidth5` and `Rule30PeriodTwoWidth6` apply it at the strip widths `5` and `6`.\n"
        "\n" + kc_sources(4, ', period-2 right half') + "\n-/\n")
s = rep(s, "namespace KC\nnamespace PeriodTwoLang\n\n"
           "open Ruliology.CellularAutomata Rule30Jen Rule30StripCertificates Rule30PeriodFourSkeleton\n",
        "namespace Ruliology.CellularAutomata\nnamespace Rule30PeriodTwoLanguage\n\n"
        "open Rule30Jen Rule30StripCertificates Rule30PeriodFourSkeleton\n")
s = rep(s, "end PeriodTwoLang\nend KC\n", "end Rule30PeriodTwoLanguage\nend Ruliology.CellularAutomata\n")
write('Rule30PeriodTwoLanguage.lean', s)

# t4: PeriodTwoW5 / PeriodTwoW6 -> Rule30PeriodTwoWidth5 / Rule30PeriodTwoWidth6
w_extra = {
    5: ("* `col1_constraints`: eventually column `1` at consecutive white times never spells `11`,\n"
        "  `00000`, `100101` (gap pair `21`) or `10010001` (gap pair `23`).\n"
        "* `free_bit_constraints`: the free bits (column `-1` at the white times) never spell the\n"
        "  complements `00`, `11111`, `011010`, `01101110`.\n"
        "\n"
        "Width `5` is the smallest strip width whose bad class forbids more than `11` and `00000`\n"
        "(computation). The constraints are conditional on an eventual period `2`; they do not exclude it.\n"),
    6: ("* `col1_constraints`: eventually column `1` at consecutive white times never spells `11`,\n"
        "  `00000`, the gap pairs `21`, `23`, `12` or the gap triples `114`, `132`, `241`, `243`.\n"
        "* `free_bit_constraints`: the same for the free bits (column `-1` at the white times),\n"
        "  complemented.\n"
        "\n"
        "The constraints are conditional on an eventual period `2`; they do not exclude it.\n"),
}
for W in (5, 6):
    s = read(f'{T4}/PeriodTwoW{W}.lean')
    s = rep(s, "import KC.PeriodTwoLang\n", "import Ruliology.CellularAutomata.Rule30PeriodTwoLanguage\n")
    s = rep(s, "that no path inside the bad class reads the listed column-`1` words at consecutive white phases.\n-/\n",
            "that no path inside the bad class reads the listed column-`1` words at consecutive white phases\n"
            "(`Rule30PeriodTwoLanguage.no_pattern`).\n"
            "\n" + w_extra[W] + "\n" + kc_sources(4) + "\n-/\n")
    s = rep(s, f"namespace KC.PeriodTwoW{W}\n"
               "open Ruliology.CellularAutomata Rule30Jen Rule30StripCertificates Rule30PeriodFourSkeleton\n"
               "open KC.PeriodTwoLang\n",
            "namespace Ruliology.CellularAutomata\n"
            f"namespace Rule30PeriodTwoWidth{W}\n\n"
            "open Rule30Jen Rule30StripCertificates Rule30PeriodFourSkeleton\n"
            "open Rule30PeriodTwoLanguage\n")
    s = rep(s, f"end KC.PeriodTwoW{W}\n", f"end Rule30PeriodTwoWidth{W}\nend Ruliology.CellularAutomata\n")
    write(f'Rule30PeriodTwoWidth{W}.lean', s)

# ---------------------------------------------------------------------------------------------
# p3-ether: namespace Ruliology.CellularAutomata.Rule30EtherThree unchanged; imports and docstrings.
FAMILY = ("The period-3 study spans the modules `Rule30EtherThree`, `Rule30EtherThreeNoWall`,\n"
          "`Rule30EtherThreeTrap`, `Rule30EtherThreeReach`, `Rule30EtherThreeLeft` and\n"
          "`Rule30EtherThreeSkeleton`, all in the namespace `Rule30EtherThree`.")

s = read(f'{P3}/P3Ether.lean')
s = rep(s, "import Ruliology\n", "import Ruliology.CellularAutomata.Rule30Ether\n")
s = rep(s, "Unlike period 4, no wall is known: `P3NoWall.no_wall_le_12` proves (kernel certificate) that no\n"
           "attachment column has a wall of width `≤ 12`, and an exhaustive C search (Rule 30 Prize project,\n"
           "period-3 study) finds none at widths `≤ 23`. The statements here are therefore a framework,\n"
           "conditional on a wall; with an empty `W`, `Absorption3` is false and the theorems are vacuous.\n"
           "For `001` a different trap exists (`P3Trap001`).\n-/\n",
        "Unlike period 4, no wall is known: `no_wall_le_12` (`Rule30EtherThreeNoWall`) proves (kernel\n"
        "certificate) that no attachment column has a wall of width `≤ 12`, and an exhaustive C search\n"
        "(Rule 30 Prize project, period-3 study) finds none at widths `≤ 23`. The statements here are\n"
        "therefore a framework, conditional on a wall; with an empty `W`, `Absorption3` is false and the\n"
        "theorems are vacuous. For `001` a different trap exists (`Rule30EtherThreeTrap`).\n\n"
        + FAMILY + "\n\n" + P3_SOURCES + "\n-/\n")
write('Rule30EtherThree.lean', s)

s = read(f'{P3}/P3NoWall.lean')
s = rep(s, "import P3Ether\n", "import Ruliology.CellularAutomata.Rule30EtherThree\n")
s = rep(s, "family of `P3Ether` has no member", "family of `Rule30EtherThree` has no member")
s = rep(s, "The exhaustive search behind the certificates (and a C search, not kernel-checked) also finds no\n"
           "wall for widths `13..23`.\n-/\n",
        "The exhaustive search behind the certificates (and a C search, not kernel-checked) also finds no\n"
        "wall for widths `13..23`.\n\n" + P3_SOURCES + "\n-/\n")
write('Rule30EtherThreeNoWall.lean', s)

s = read(f'{P3}/P3Trap001.lean')
s = rep(s, "import P3Ether\n", "import Ruliology.CellularAutomata.Rule30EtherThree\n")
s = rep(s, "The period-3 ether admits no wall of width `≤ 12` (`P3NoWall`; a C search finds none up to width\n"
           "`23`). Instead, the right half driven by `001^∞` can form a different structure: a strip of `47`\n"
           "columns next to the center whose first `38` columns repeat with period `21`, shielded on the right\n"
           "by `9` columns that absorb every input. `t001` lists its `815` states, each with a time label\n"
           "modulo `21`; it is closed under both values of column `48`, and at the white phases of the center\n"
           "column `1` is a fixed function `u` of the label.\n",
        "The period-3 ether admits no wall of width `≤ 12` (`Rule30EtherThreeNoWall`; a C search finds none\n"
        "up to width `23`). Instead, the right half driven by `001^∞` can form a different structure: a\n"
        "strip of `47` columns next to the center whose first `38` columns repeat with period `21`, shielded\n"
        "on the right by `9` columns that absorb every input. `t001` lists its `815` states, each with a\n"
        "time label modulo `21`; it is closed under both values of column `48`, and at the white phases of\n"
        "the center column `1` is a fixed function `u` of the label.\n")
s = rep(s, "  half driven by `w^∞` enters the trap, the center column is not eventually `w^∞`. Whether this\n"
           "  holds for `001` is open (see the period-3 report: many but not all tested right halves enter\n"
           "  within the horizons tried).\n",
        "  half driven by `w^∞` enters the trap, the center column is not eventually `w^∞`. Whether this\n"
        "  holds for `001` is open; in the period-3 study all `18,258` tested right halves entered `t001`,\n"
        "  with delays up to about `2 · 10^5` steps (computation, not a proof).\n")
s = rep(s, "Sources: the Rule 30 Prize project (2026), period-3 study.\n-/\n", P3_SOURCES + "\n-/\n")
write('Rule30EtherThreeTrap.lean', s)

s = read(f'{P3}/P3Reach.lean')
s = rep(s, "import P3Trap001\n", "import Ruliology.CellularAutomata.Rule30EtherThreeTrap\n")
s = rep(s, "A sanity anchor for `P3Trap001`: the trap `t001` is not vacuous. The empty right half, driven by\n"
           "`001^∞` from phase `0`, is in the trap at time `1270` (`t001_reached`), i.e. it satisfies the\n"
           "conclusion of `AbsorptionT t001` for this one start (`absorbed_empty`).\n",
        "A sanity anchor for `Rule30EtherThreeTrap`: the trap `t001` is not vacuous. The empty right half,\n"
        "driven by `001^∞` from phase `0`, is in the trap at time `1270` (`t001_reached`), i.e. it satisfies\n"
        "the conclusion of `AbsorptionT t001` for this one start (`absorbed_empty`).\n")
s = rep(s, "* `t001_reached`: kernel computation of `1270` steps, then a lookup in the trap.\n-/\n",
        "* `t001_reached`: kernel computation of `1270` steps, then a lookup in the trap.\n\n" + P3_SOURCES + "\n-/\n")
write('Rule30EtherThreeReach.lean', s)

s = read(f'{P3}/P3Left.lean')
s = rep(s, "import P3Ether\n", "import Ruliology.CellularAutomata.Rule30EtherThree\n"
        "import Ruliology.CellularAutomata.Rule30DrivenLeft\nimport Ruliology.CellularAutomata.Rule30PeriodTwo\n")
s = rep(s, "`W ≤ 70` violates the `011` constraint by time `99` (all three phases).\n-/\n",
        "`W ≤ 70` violates the `011` constraint by time `99` (all three phases).\n\n" + P3_SOURCES + "\n-/\n")
write('Rule30EtherThreeLeft.lean', s)

s = read(f'{P3}/P3Skel.lean')
s = rep(s, "import P3Left\n", "import Ruliology.CellularAutomata.Rule30EtherThreeLeft\n"
        "import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton\n")
s = rep(s, "Consequence for the left half (`P3Left`):", "Consequence for the left half (`Rule30EtherThreeLeft`):")
s = rep(s, "Sources: the Rule 30 Prize project (2026), period-3 study; certificates generated by a modified\n"
           "`skel_export.py` (round 2).\n-/\n",
        "Sources: the Rule 30 Prize project (2026), final batch (2026-10-15): period-3 study\n"
        "(`p3-ether`), certificates generated by a modified `skel_export.py` (round 2); adversarially\n"
        "verified.\n-/\n")
write('Rule30EtherThreeSkeleton.lean', s)

for p in written:
    print(p)
