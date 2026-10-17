# Rule 30 Prize, Problem 1: attempt of 2026-10-15

Problem 1 asks whether the center column of rule 30, started from a single black cell, is eventually periodic. The conjecture is that it is not.

The Lean statement is `Ruliology.CellularAutomata.Rule30Prize.Problem1` in the kit's [`lean/Ruliology/CellularAutomata/Rule30Prize.lean`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Prize.lean). It matches formal-conjectures' `Other/Rule30.lean`.

**Write-up:** <https://sw1sh.github.io/vibe-proof/rule30-prize/>. It is published with GitHub Pages from the `gh-pages` branch; the source is [`writeup/rule30-state.html`](writeup/rule30-state.html).

**Outcome: Problem 1 is still open.** A coordinator and about 100 subagents ran two research rounds, a final batch and a consolidation. Each round had adversarial verification. This folder holds:

- the write-up;
- the complete working record;
- the Rule 30 Prize kit, as the submodule [`kit/`](https://github.com/WolframInstitute/Rule30PrizeKit). The kit is the single home of all the Lean: the statements, the partial results and the equivalent forms. This folder keeps no other copy.

Every Lean result uses only `propext`, `Classical.choice` and `Quot.sound`. None uses `sorry` or `native_decide`.

## Status by period

| Case | Status | Lean (the kit's `lean/`, namespace `Ruliology.CellularAutomata.*`) |
|---|---|---|
| Period 1 | **Proved** for every column | `Rule30Prize.no_column_eventually_constant`, `center_not_eventually_period_one` |
| Small periods | **Proved:** no eventual period P ≤ 4096 with transient ≤ 8192 | `Rule30Window` |
| Any period | **Proved:** T + P ≥ 16359 | `Rule30FactorWindow` |
| Period 2 | Reduced to Q01, a statement about the zero-boundary left half. Q01 is **open** in general. It is proved in Lean for every start of width ≤ 52, and ≤ 56 in a module the default build skips. | `Rule30PeriodTwo`, `Rule30PeriodTwoCoupled`, `Rule30PeriodTwoSideways`, `Rule30ZeroBoundary*`, `Rule30ZeroBoundaryWidth52`, `Rule30ZeroBoundaryWidth56`, `Rule30PeriodTwoWidth5/6` |
| Least period 3 | Reduced. 001 needs one of AbsorptionT t001, Q001 or C3s001. 011 needs C3w(011). All four are **open**. | `Rule30EtherThree*` |
| Least period 4 | Reduced to Absorption, the ether-and-wall trap, which is **open**. The pure ether lies in no trap of width ≤ 20. | `Rule30Ether`, `Rule30PeriodFourSkeleton`, `Rule30EtherTrapWidth20` |
| Longer periods | **Open.** Some words are excluded, for example by long black runs and 30 certified words. | `Rule30BlackRuns`, `Rule30BlackRunBlocks`, `Rule30StripCertificateTable`, `Rule30WhiteRunEight` |

Barriers are also proved:
- Rules 90, 150 and 210 share every structural fact the argument uses, yet their center columns are eventually constant (`Rule30Realization`).
- Local, strip, finite-state, additive and edge-DFA invariants cannot prove Q01 (`Rule30ZeroBoundaryBarriers`).

## Layout

- **[`kit/`](https://github.com/WolframInstitute/Rule30PrizeKit):** the Rule 30 Prize kit, a submodule of the public repository [WolframInstitute/Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit). Run `git submodule update --init` to check it out. It holds all the Lean:
  - [`lean/`](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/lean): the official statements and the catalog of partial results, 54 modules in core Lean 4.30.0. They were copied on 2026-10-15 from the `ruliology-lean` catalog, which git does not track; [`SHA256SUMS`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/SHA256SUMS) lists their hashes, which match the integration manifest `research/integrate-final/catalog_after.sha256`.
  - [`equivalents/`](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/equivalents): 41 statements proved equivalent to Problem 1 in Lean 4 + Mathlib, as 118 `problem1_iff_*` theorems, and 9 sufficient conditions (`problem1_of_*`), for example the irrationality of the binary number 0.c(0)c(1)c(2)…, and a [catalog](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/CATALOG.md) of all 53 known equivalent forms.
  - the submission template and the checker that the Prize's verifier runs.
- **[`TECHNIQUES.md`](TECHNIQUES.md):** a portfolio of recent (2024–2026) proof techniques that touch the equivalent forms, many of them AI-assisted and from other projects, with a ranked shortlist of next experiments.
- **[`writeup/rule30-state.html`](writeup/rule30-state.html):** the full write-up, a self-contained page. Read it at <https://sw1sh.github.io/vibe-proof/rule30-prize/>.
  - Section 9 covers the final batch.
  - Appendix A is the table of 393 theorems with their axioms.
  - Appendix B lists the computational claims.
- **[`deepdive/`](deepdive/NOTES.md):** a follow-up study (2026-10-17) of Ψ(∅), the simplest open instance of the coupled period-2 problem CQ01, and of the memory needed to compute the center column. C programs and notes; it found no exploitable structure.
- **[`agents/`](agents/README.md):** the Prize's agent program: the instructions for agents, the submission API and the Lean verifier.
- **`research/`:** the working record, one folder per agent task. It is frozen: proofs that matter live in the kit.

  | Phase | Folders |
  |---|---|
  | Briefs | `BRIEF.md`, `BRIEF2.md`, `FINDINGS-coordinator.md`: definitions, constraints, state after round 1 |
  | Agent results | `results/`: every agent's structured result per run (`round1.json`: 62 agents; `round2.json`: 20; `consolidation-r2.json`; `final-batch.json`; `integration-final.json`; `archive-audit.json`) |
  | Orchestration | `workflows/`: the scripts that launched the agents, with their prompts |
  | Coordinator | `scripts`, `window`, `driven`, `period2` |
  | Literature | `literature`, `jen-lit`, `lit-oss`, `lit_theory`, `lit-recent` (scripts and notes; `lit-recent/NOTES.txt` is the summary) |
  | Round 1, attacks | `absorb-right`, `generalize-jen`, `left-consistency`, `diagonal`, `smallperiods`, `gf2-algebra`, `complexity`, `newideas` |
  | Round 1, verification | `verify-*` (43 folders, 05:31–06:40), `mh-rigor-verify`, `verify_mahler_rigor` |
  | Round 1, curation | `curation` (axiom checks of the staged modules), `synth-lead`, `verify-cone-agree-rigor`, `verify-lemmaAstar-rigor`, `verify-lemmaA-nine-black-rigor` |
  | Round 2, programs | `A-reconmap`, `A-monovariant`, `A-invsearch`, `progA-backdet` (period 2); `progB-avoid`, `B-edge-trap` (period 4) |
  | Round 2, verification | `V-*`, `verify-A1*`, `verify-A2*`, `verify-B1*`, `verify-b2-rigor` |
  | Round 2, wrap-up | `synth-r2`, `integrate-r2`, `writeup-r2` (the write-up's generator), `consolidate_args.json` |
  | Final batch | `final_tasks`, `final_args.json`, `kernel-certify-r2`, `p3-ether`; each has a `REPORT.md` that includes its verification |
  | Integration | `integrate-final`: evidence that integrating into the catalog changed only names; `snapshot`: build and axiom logs for the `lean/` snapshot, now the kit's `lean/` |
  | Equivalents | `equivalents-survey`: the surveys behind the kit's catalog of equivalent forms and `TECHNIQUES.md`, the two batches' worker and verifier reports, the attack panel, and the survey's scratch statement files (`sorry`, not built) |

## Reading the research folders

- Notes, reports and scripts refer to paths such as `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/X`. That is the scratch area this folder was copied from; `X` is now `research/X`.
- The scripts record what was run; most will not run as they are. Many hard-code those scratch paths, or read `/Users/swish/src/wolfram/Ruliology/build/rule30/center-1e7.bin`, which is outside this repo. The exceptions are `research/kernel-certify-r2/t1/build.sh` and `buildall56.sh`.
- Research Lean files import `Ruliology.*`. Most compile from the kit's `lean/` (`cd kit/lean`) with `lake env lean <file>`; a few also need staged modules on `LEAN_PATH`. Some refer to the `lean/` snapshot that this folder held until 2026-10-17; it is now the kit's `lean/`.
  - Some are negative controls that are meant to fail, for example `verify-noleftabs/Bogus.lean`, `verify-p4traps-rigor/neg*.lean` and `p3-ether/tmp/neg/`.
  - Never glob `research/**/*.lean` into a build.

## Corrections recorded by the verifiers

- **Round 1, generalize-jen:** the corollary C3 has an off-by-one in its gap threshold. `verify-c3-doubling/C3Check.lean` (`sx_not_cover`) refutes it in Lean, and it never reached the catalog.
- **Round 1, complexity:** the agent claimed that every word of length n ≤ 20 occurs in the center column, p_c(n) = 2^n. This fails at n = 20: 96 of the 2^20 words are absent from the first 10^7 bits (`mh-rigor-verify/recount.py`).
- **bv_decide files:** `verify-white0r11-rederive/BV*.lean` and `verify-white0r11-rederive/r6/R6Full.lean` use `bv_decide`, which trusts the compiler through `Lean.ofReduceBool`. They are below the catalog's standard, and none is in `lean/`.
- **Integrated later:** `verify-white0r11-rigor/StandaloneGe8.lean` is checked and strengthens `Rule30BlackRuns.no_white_run_11` from r ≥ 10 to r ≥ 8. It stayed out of the catalog; since 2026-10-17 it is the kit's `Rule30WhiteRunEight`, as is the width-56 check of `kernel-certify-r2/t1` (`Rule30ZeroBoundaryWidth56`).
- **Final batch:** some claims in the workers' summaries were refuted or narrowed, and each `REPORT.md` lists them under "Refuted or unverified claims". For example, p3-ether's "no wall exists" holds only up to width 12 in Lean and width 28 by search.

## Not committed

`.gitignore` in this folder keeps the following out of git. The files stay in the local folder.

- **Third-party text:**
  - plain-text extracts of papers (`research/literature/*.txt`);
  - OCR of Jen's 1990 report (`research/jen-lit/ocr1990/`);
  - copies in `research/lit-oss/`: Condrey and Das extracts, and a theorem list from the Dibujaron repository.
- **`research/lit-oss/codesearch2.tsv`:** every GitHub code search failed with HTTP 403 (rate limit). So the survey of third-party repositories rests on name and description searches (`search_*.tsv`) and on hand-picked downloads, which were not archived.
- **Bulk generated data over 250 KB,** regenerable:
  - `research/progB-avoid/bad_<w>_<b>.txt`: `cc -O2 -o scc_an scc_an.c && ./scc_an <w> <b> bad_<w>_<b>.txt`, under 2 s each;
  - `research/gf2-algebra/cols200k.txt`: `cc -O2 -o r30cols r30cols.c && ./r30cols 200000 1 > cols200k.txt`;
  - `research/integrate-final/verify/all_names.txt`: run `DumpNames.lean` in the same folder.
- **Empty captures of aborted runs.**

Downloads, build outputs and binaries were never copied here.

## Rebuilding

- **The Lean:** see the kit's README. From `kit/`: `sh setup.sh`, then `lake build`.
- **Q01 for width ≤ 56:** the kit's `Rule30ZeroBoundaryWidth56`; its `lean/README.md` says how to build it, one chunk module at a time, about 6 minutes in all. The archived run can also be replayed: `zsh research/kernel-certify-r2/t1/buildall56.sh` compiles its 64 chunk files against the kit's `lean/`, at about 5.4 s and 1.5 GB each. New logs go to `t1/build/logs/`, which git ignores.
