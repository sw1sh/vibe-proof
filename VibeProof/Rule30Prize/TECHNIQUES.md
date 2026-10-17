# Rule 30 Problem 1: proof techniques from 2024–2026, and what to salvage

## Summary

**No technique from 2024–2026, with or without AI, excludes any nonconstant eventual period of the rule 30 centre column. Nothing in this portfolio rates high.**

- The only settled case is period 1, an eventually constant column. Condrey settled it for every nonzero finite configuration ([arXiv 2609.09431](https://arxiv.org/abs/2609.09431), preprint), and rule30-foundry agents formalised it in Lean, which we did not rebuild. Our catalog proves the single-seed case.
- Period 2 is the next open case. Every serious project, whether run by people or by AI agents, stopped at the same point: showing that a finite orbit must eventually break a constraint whose set of allowed behaviours has positive entropy.
- Frontier AI provers have not reached statements of this kind. Their verified results on related problems are short arguments, explicit constructions and closed forms for structured sequences.

**What is still worth salvaging**, in the order the audit recommends (details in the shortlist, §3):

1. **Exact light-cone realizability for the coupled period-2 problem CQ01.** It is checked by SAT at bounded left width, and each long forbidden word goes into Lean as an LRAT certificate that the kernel replays (card D12, item S1). It sees right-half constraints of every length at once. The longest-lived left starts under the old short-word filter die much earlier under it: at width 96, all 103 of them (filtered deaths 110–116) die by time 87, and the one that lasted to 116 under the filter dies at about 57. It measures what a proof of CQ01 has to beat. It does not prove anything about period 2 by itself.
2. **Axiom-free CC0 Lean by Ralf Stephan with Claude Code** (A1, B3, A5; S2). These are cheap and certain library entries. The Stanley engine turns the `p-recursive` and `fatou` forms of [CATALOG.md](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/CATALOG.md) into theorems, and shows that holonomic methods cannot apply to Σ c(t)zᵗ. Only some of the files are axiom-free; the others import cited axioms (table in A1). The Hankel and 2-adic forms are already re-derived in [LinearRelations.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/LinearRelations.lean) and [TwoAdic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TwoAdic.lean).
3. **A census of excluded period words across three engines** (Berzai's, placego's and ours; C1, F14; S3). The exclusions are unconditional, hold for every finite seed and port to kernel certificates, and the engines complement each other. None of them has reached a primitive word of length 2–7.
4. **The Duhamel–Cartier decomposition, as a long shot** (B1; S4). It is the only global algebraic handle that lies outside the local barriers. But rule 54 has the same structure and a periodic centre, so any invariant must detect the chirality of rule 30's nonlinear term, and it must use the finiteness of the seed.

**Demoted:** filtering the left-half search with short minimal forbidden words of the period-2 right-half language, which was the first item of the draft (D2, S9). That language has minimal forbidden words of length 18 and 37. The plateau seen at short lengths is therefore an artefact, and a bit-sliced kernel check of all 2^(2L−1) windows is out of reach at those lengths. Item 1 replaces it.

**Also kept:** verification hygiene (replay under Lean v4.35.0 with Comparator), the barrier theorems as filters (§0.5), and counterexample-first tests of the open sub-hypotheses (S8).

---

## 0. About this file

### 0.1 Sources and scope

Compiled 2026-10-15 for the equivalents library, then at `VibeProof/Rule30Prize/equivalents` and now the [`equivalents/`](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/equivalents) folder of the Rule 30 Prize kit (Lean 4.30.0, Mathlib `c5ea003`).

- Six surveys produced 117 technique cards: Rule 30 projects; irrationality and transcendence; words and automata; dynamics and non-periodicity; frontier-AI mathematics; and our own archive.
- A synthesis merged them, removed duplicates, checked each technique against our barrier theorems and ran its own checks (Appendix B).
- An independent audit then checked that draft against primary sources (the arXiv API, the GitHub API, erdosproblems.com, 1stproof.org, the Lean release notes and the downloaded sources) and re-ran its computations. This version applies the audit's 18 corrections, adds its 7 missing techniques (C10, D12–D15, E10, E11) and follows its salvage order. Appendix C lists each correction and where it was applied.
- The raw cards, the draft and the audit are in [research/technique-survey.json](research/equivalents-survey/technique-survey.json).
- Downloaded third-party code was read but never executed.

### 0.2 Where the equivalent forms are

[CATALOG.md](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/CATALOG.md) lists the equivalent, stronger, weaker and related forms of Problem 1 under ids such as `two-adic` or `p-recursive`. The cards below name forms by these ids. The Lean library [Rule30Equivalents/](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/equivalents/Rule30Equivalents) proves `Problem1 ↔ X` for many of them:

| File | Forms (CATALOG.md ids) | Example theorems | Cards |
|---|---|---|---|
| [Basic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/Basic.lean) | the definition | `problem1_iff_not_eventuallyPeriodic` | all |
| [BinaryIrrational.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/BinaryIrrational.lean) | `binary-irrational`, `base-b-irrational` | `problem1_iff_irrational_binary`, `problem1_iff_irrational_base` | A3, A4, A9 |
| [NumberTheory.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/NumberTheory.lean) | `continued-fraction`, `dirichlet-liouville`, `circle-rotation`, `integer-digits` | `problem1_iff_cf_not_terminates`, `problem1_iff_liouvilleWith_two`, `problem1_iff_not_rational_digits` | A3, A9 |
| [TwoAdic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TwoAdic.lean) | `two-adic`, `fcsr-complexity` | `problem1_iff_padic_irrational`, `problem1_iff_two_adic_complexity` | A2, A6, C10 |
| [PowerSeriesF2.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/PowerSeriesF2.lean) | `series-f2-lfsr` | `problem1_iff_series_not_rational`, `problem1_iff_linear_complexity_unbounded` | B1, B3, F9, F15 |
| [LinearRelations.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/LinearRelations.lean) | `rational-any-field`, `linear-relations`, `hankel` | `problem1_iff_series_not_rational` (any field), `problem1_iff_hankel_det_zmod_two`, `problem1_iff_hankel_det_int` | A1, B3 |
| [ShiftOrbit.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/ShiftOrbit.lean) | `shift-orbit`, `morse-hedlund` | `problem1_iff_injective_shifts`, `problem1_iff_ncard_factors` | A5, B4, C3, F15 |
| [WordsAutomata.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/WordsAutomata.lean) | `eventual-word`, `mathlib-bridges`, `special-factors`, `orbit-closure`, `omega-limit`, `tail-language`, `finite-state-machines`, `nlfsr` | `problem1_iff_no_word`, `problem1_iff_no_primitive_word`, `problem1_iff_right_special`, `problem1_iff_no_feedback_shift_register` | C1, C10, F1–F4, F14 |
| [TransformsSeeds.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TransformsSeeds.lean) | `fc-bridge`, `pi2-normal-form`, `simple-transforms`, `decimations`, `stripe-seeds` | `problem1_iff_fc`, `problem1_iff_pi2`, `problem1_iff_stripeSeed` | B4, D1 |
| [Symmetry.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/Symmetry.lean) | `symmetric-rules` | `problem1_iff_rule86`, `problem1_iff_rule135` | F1 |

- The library was built in two batches: BinaryIrrational, PowerSeriesF2, ShiftOrbit and Symmetry first, then NumberTheory, TwoAdic, LinearRelations, WordsAutomata and TransformsSeeds. [Rule30Equivalents.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents.lean) imports all ten files. CATALOG.md marks these forms "Proved (library)" after an independent verifier recompiled each module and checked its axioms; [scripts/CheckAxioms.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/scripts/CheckAxioms.lean) prints the axioms of every `problem1_iff_*` theorem.
- Forms touched here that are not yet in the library: `p-recursive` and `fatou` (A1), `natural-boundary` (A7), `cobham-christol` (B1, B2, B4), `coupled-halves` (D12), `nks-integer-rows` (A2), `return-words` (A3) and `diagonal-array` (F12), all only stated in CATALOG.md, and reflection complexity (C3), which is not in CATALOG.md yet.
- CATALOG.md also lists the stronger statements (no column eventually periodic, FinConf, NumberLike, LHC, non-automaticity, unbounded runs) and the project's period reductions (Q01, CQ01, Absorption), which are not implied by Problem 1. Most techniques here attack those.
- The project's core Lean (no Mathlib), with the period reductions and the barrier theorems, is in [../lean/Ruliology/CellularAutomata/](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/lean/Ruliology/CellularAutomata).

### 0.3 Glossary

- **c(t)**: the centre column of rule 30 (new cell = l ⊕ (c ∨ r)) started from one black cell: 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, … (OEIS A051023). Problem 1 says c is not eventually periodic.
- **Eventual period word w**: a word with c = w^∞ from some time on. `problem1_iff_no_word` states that Problem 1 holds iff no nonempty word is one. *Black* and *white times* are the times where the hypothesised tail reads 1 and 0.
- **Effective boundary**: the left half sees column 0 only through c(t) ∧ c(t+1) (`effective_step`).
- **ZBL, Q01 and CQ01**: the ZBL is the zero-driven left half: rule 30 on the columns left of 0, with column 0 held white. Q01 says every finitely supported ZBL start eventually has column −1 white at an even step. **CQ01** is the coupled version, faithful to the problem, in which both halves are finite. In Lean, Q01 ⇒ CQ01 ⇒ no eventual period 2. Neither is implied by Problem 1.
- **Θ(f)**: the unique ZBL start whose column −1 at the white times reads f. Q01 holds iff Θ(f) is never finitely supported.
- **u**: column 1 read at the white times beside a 0101 centre. Under period 2, u = ¬f (`p1_odd`).
- **Light-cone language, MFW**: the light-cone language is the set of length-L words u₀…u_{L−1} that some right window of width 2L−1 produces. A *minimal forbidden word* (MFW) is absent from it while its prefix and its suffix are present.
- **D(W) and D_exact(W)**: D(W) is the latest death time over ZBL starts of width W (the Q01 search). D_exact(W) is the same in the coupled problem, where u must be produced by some finite right half (D12).
- **Absorption(w)**: every finite right half driven by w^∞ eventually enters a closed, consistently labelled trap.
- **Ether, wall**: an ether is a rule-30 pattern, periodic in space and time, whose columns carry candidate period words. A wall is a set of strip states that is closed under every far input.
- **c7**: the 7×4 ether (F4) placed so that column 0 alternates. It is an infinite configuration that meets every period-2 constraint (`ether_coupled_witness`).

### 0.4 Card format and labels

Each card gives its origin (people, date, URL), the AI involvement, what was proved, the verification status, the forms it touches (CATALOG.md ids and library files), the core idea, a transfer plan for rule 30, the obstacle, the artifacts with their licences, and a promise rating. The line under each card title gives the promise and the verification status.

| Verification label | Meaning |
|---|---|
| **Lean (ours)** | In our catalog or library, with axioms re-printed: only `propext`, `Quot.sound`, `Classical.choice`. |
| **Formal (3rd party)** | Machine-checked by its authors; **not rebuilt by us**. |
| **Static scan** | We scanned the import closure for `axiom` declarations; nothing was built. |
| **Peer-reviewed** | Journal or refereed conference. |
| **Preprint** | arXiv, Zenodo or repository write-up. The card says what we reproduced. |
| **Computed** | A finite computation: evidence, not proof. |
| **Derived here** | An argument first written in this portfolio; not machine-checked. |
| **Announced** | A claim without a checkable artifact. |
| **Refuted** | Shown to be wrong. |

**Promise** rates how much a technique can contribute to *proving* Problem 1 or an equivalent form: high, medium, low or none. When a technique mainly adds library entries or infrastructure, the card rates that value separately. **Nothing in this portfolio rates high.**

### 0.5 Barriers used as filters, and what each one covers

Proved in Lean (ours):
- **F-OR**: rules 90, 150 and 210 share Jen's theorem, the light-cone edge, the power-of-two right-diagonal periods and the odometer, yet their single-seed centres are eventually constant (`Rule30Realization.barrier`). A valid argument must therefore use rule 30's OR.
- **F-FIN**: every column, paired with every right half, is realised by exactly one configuration, which is usually infinite (`column_realizable_unique`). A valid argument must therefore use finiteness.
- **B1, B6 (Q01 only)**: no finite abstraction, and no automaton reading from the edge, gives a ranking for Q01 (`finite_abstraction_has_lasso`, `no_edge_dfa_ranking`). The witnesses are truncated stripes.
- **B2 (Q01 only)**: no function of (width, wall window, edge window) decreases along every surviving double step (`no_local_ranking`).
- **JointBarrier (two-sided)**: on ℤ, from arbitrary finite configurations, no function of (outermost black positions, centre window, edge windows) decreases at every flip of the centre (`no_joint_local_ranking`). The witnesses are truncations of c7. **This is the only proved barrier for the two-sided setting.**
- **Edge region**: edge structure, together with windows shorter than the distance to the wall, carries no information (`edge_region_barrier`). Backward trees never die (`barrier_exists`, `barrier_unique`).

All of these are in [Rule30ZeroBoundaryBarriers.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryBarriers.lean), [Rule30Realization.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Realization.lean), [Rule30ZeroBoundary.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean) and [Rule30DrivenLeft.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30DrivenLeft.lean).

Computed or derived:
- **C6** (computed): no nontrivial additive conservation law exists for rule 30 up to range 10, or for rule 30² up to range 8.
- **B7** (derived here, card D8; not machine-checked): no additive ranking of range ≤ 8 certifies Q01. A two-sided variant, built on JointBarrier and C6, bars additive rankings that decrease at every flip of the centre.
- **Local obstruction** (computed; Lean `word_lemma` for the ether): no strip certificate exists for any primitive word of length 2–7 at width ≤ 16 (≤ 20 for 0001), or of length 9 at width ≤ 16.

**Not proved**, and labelled as such wherever a card uses them:
- a finite-abstraction (lasso) barrier for **CQ01** along truncations of c7. It is a conjecture (D9);
- any barrier for **Absorption**. None is known; trap-avoiding strip paths keep the full growth rate (computed);
- whether B7's argument extends to Absorption. Nobody has checked.

B1, B2 and B6 apply to Q01 only: their witnesses have free bits starting with 11111, which a real period-2 tail forbids.

### 0.6 Licences

"No licence" means all rights are reserved: re-derive the code, or ask before copying it. The audit checked most of these against GitHub:
- **CC0-1.0**: rwst/Ceiling-Orbits, rwst/Transcendence-Criteria, rwst/Antihydra-Basics, rwst/Confinement-Certificates.
- **Apache-2.0**: rwst/Subspace-Theorems (not CC0), formal-conjectures, openai/math, openai/ten-proofs, alphaproof-nexus-results, Seed-Prover, LeanMarathon, dcondrey/blindmind, plectis-erdos-lean.
- **MPL-2.0**: Berzai's rule30-left-edge.
- **MIT**: wryan2986/rule30-lab, Cliff-Lee/R30, Fomin's code, Aeacu2/Automata, epoch-research/LeanOpenProblems (GitHub reports NOASSERTION), Coq-BB5 (only `CoqBB5/LICENSE`; no root licence).
- **BSD-2-Clause**: mfornet/busybeaver (in `LICENSES/`). **0BSD**: carrino/Coq-BBB4. **GPL-3.0**: Walnut.
- **CC BY 4.0**: Condrey; Nersissian (arXiv and the Zenodo U-series); Kim; Fomin's papers; Howe; Cavalcante. **CC BY-NC 4.0**: Woffinden. **CC BY-NC-SA 4.0**: Nersissian, Zenodo 18921456.
- **No licence**: placego, rule30-foundry, cochon123, Dibujaron, avikj, eliottcassidy2000, beetree/math_erdos_251, ConwayTransducer, emreyolcu/rewriting-collatz, xrchz/CollatzLean. Our own repository, sw1sh/vibe-proof, also has no licence file.

---

## 1. Orientation

### 1.1 Where every project stopped

- **Every serious project stopped at the same wall**: every orbit of a positive-entropy constrained system must eventually violate a constraint. Each group words it differently:
  - placego: "no emptiness from a constrained side of positive entropy";
  - rule30-foundry: no transport bound from local u-bans to unbounded left weight;
  - Berzai: an interface language of positive entropy, which defeats every window size;
  - Fomin: a discrepancy problem for one orbit.
- **placego** (Claude Local and Cloud, GPT and Kimi agents) recorded a joint halt on 2026-10-14 at 13:45 BST and a second halt on 2026-10-15 at 14:58 BST (`NOW.md`). Its swarm SW-01 judged 10 proposals: none survived, 2 were wounded and 8 died. Only proposals #3, #9 and #10 concerned rule 30; the two wounded ones were about Erdős's ternary digits of 2ⁿ. So SW-01 says little about rule 30 in particular.
- **Frontier provers have not reached this kind of statement.** AlphaProof Nexus attempted ten irrationality or digit problems and solved none of them. On FrontierMath Erdős the best model solved 2 of 68 curated open problems at $300 (1.4).

### 1.2 Technique families and the forms they reach

| Family | Main cards | Forms reached | Verdict |
|---|---|---|---|
| Word-exclusion engines: a finite over-approximation of the right half, then (masked) Jen | C1, F14, E11 | `eventual-word`, one word at a time; NumberLike and FinConf word by word | Unconditional for long words (length ≥ 8). They do not reach primitive words of length 2–7 at the widths searched (computed). |
| Coupled and left-half reductions | D2, D3, D12, F2, F3, F5, F11 | `eventual-word` for periods 2–4, through Q01, CQ01 and Absorption | The frontier. Both halves have positive entropy. Exact realizability (D12) is the sharpest measuring tool. |
| Algebraic series methods | A1, A2, A7, B1–B4, C10 | `series-f2-lfsr`, `rational-any-field`, `hankel`, `two-adic`, `p-recursive`, `fatou`, `cobham-christol` | Equivalences are cheap. A proof needs an invariant that takes infinitely many values, and nobody has one. |
| Arithmetic irrationality | A3–A6, A9 | `binary-irrational`, `base-b-irrational`, `two-adic`, `hankel` | Zero margin for 0/1 digits. These methods need analytic or multiplicative structure that c lacks. |
| Dynamics certificates | D6–D11, D13 | Q01, CQ01, Absorption, finite windows | For Q01, finite-state rankings are barred (B1, B6) and so are additive ones (B7, derived). For CQ01, only local rankings at centre flips are barred (JointBarrier), plus additive ones (B7 two-sided, derived). For Absorption nothing is barred. SAT only extends finite cases. |
| Exact descriptions and physics vocabulary | D14, D15, F10 | `eventual-word`, through exact descriptions of the driven halves | No zero-entropy description has been found beyond the boundary layers. |
| AI workflow patterns | E1–E11 | any Lean statement | Tooling; no mathematics of its own. |

### 1.3 One object, many names

| Object | Our archive | placego | rule30-foundry | Berzai | Others |
|---|---|---|---|---|---|
| Forced left half under period 2 | Θ(f); Q01 ⇔ LR ⇔ BWR; D(W) | LR, R(d), R_real(d) | completion(u,N), W_N, L1–L4 | – | Kim's inverse layers; Woffinden's thread; eliottcassidy2000 THM-4048 |
| Column 1 at white times beside 0101 | u; block law; width-5/6 laws | visible column 1; "the wheel"; channel bound | u-language, 12 MFWs | interface language L(01) | audit: MFWs of length 18 and 37 |
| Exact realizability of u | audit's z3 scripts | R_real by kissat, cake_lpr-checked cuts | free-input SAT minima (DRAT) | – | – |
| Defect identity L_{t+p} ⊕ L_t = (1 ⊕ C_t)(R_{t+p} ⊕ R_t) | masked Jen, `effective_step` | – | – | interface identity | Condrey's time-shift defect; Kim; the transferred Antihydra argument |
| Rule 30 = rule 150 ⊕ (c ∧ r) | ANF note (paper) | – | forcing identity | Duhamel formula | control: rule 54 = rule 150 ⊕ (l ∧ r) |
| Jen with a clock | `jen_clock` | Theorem A | – | – | – |
| Word exclusion by a finite right strip | strip and rank certificates | strip graphs, stable sets | – | K-window automaton | cochon123; first posted as a target by Ikram (OSF, 2026-05-15) |
| Period 1 for finite configurations | single-seed proof via Jen | entry 37 | 50 Lean declarations | – | Condrey |
| 2-adic presentation | right-edge odometer; `TwoAdic.lean` | §8.77 T-function | – | remark | wryan2986; Stephan's ℤ₂ digits (imports axioms) |
| Kill records | barrier theorems | SW-01, §8.116 | CLAIM_LEDGER | 27-route closed table | Condrey's roundtable; Fomin's assaults; Howe's 12 routes |

### 1.4 How far AI claims hold up

- **Aletheia's Erdős sweep** ([arXiv 2601.22401](https://arxiv.org/abs/2601.22401)): of 200 graded answers, 63 were technically correct and 13 (6.5%) were meaningful.
  - The v3 full text ([HTML](https://arxiv.org/html/2601.22401v3)) splits the 13 into 4 novel answers (#652 and #1051 in full, #654 and #1040 in part) and 9 found in or rediscovered from the literature (rediscoveries #397, #659, #935, #1089; identifications #333, #591, #705, #992, #1105). The v3 abstract and listing comment still say 5 and 8.
  - The authors call none of the novel answers paper-level. That is contestable: #1051 seeded the paper of Barreto, Kang, Kim, Kovač and Zhang, which is to appear in Bull. LMS.
- **AlphaProof Nexus** ([arXiv 2605.22763](https://arxiv.org/abs/2605.22763)) resolved 9 of 353 Erdős statements and 44 of 492 OEIS conjectures. It attempted #68, #243, #247, #251, #257, #264(ii), #267, #269 (a variant), #1049 and #406, all irrationality or digit problems, and solved none.
- **FrontierMath Erdős** ([arXiv 2609.25050](https://arxiv.org/abs/2609.25050)): the best model, GPT-6 Astra, solved 2 of 68 at $300, and 5 of 68 with more than $220k of compute.
- **OEIS Open** ([arXiv 2608.11941](https://arxiv.org/abs/2608.11941)): 147 of 492 conjectures settled at $50 per attempt. Our survey said no model resolved A214560, the conjecture that the number of 0s in binary n² tends to infinity (a digit-growth statement, not a randomness one). The audit did not find that claim in the paper, so it is unverified.
- **First Proof** ([1stproof.org](https://1stproof.org)):
  - Batch 1 (February 2026) had two separate results, which the draft mixed up. In the organisers' pre-release test of public models only problems 9 and 10 were answered correctly ([Scientific American, 2026-02-14](https://www.scientificamerican.com/article/first-proof-is-ais-toughest-math-test-yet-the-results-are-mixed/)). OpenAI's internal model claimed 6 "likely correct" answers and revised that to 5 (problems 4, 5, 6, 9 and 10) after problem 2 was withdrawn ([OpenAI, 2026-02-20](https://openai.com/index/first-proof-submissions/)).
  - Batch 2: ProofCouncil, 6 of 10 ([arXiv 2607.09474](https://arxiv.org/abs/2607.09474), which reports batch 2, not batch 3).
  - Batch 3 (results on 2026-10-14): ProofCouncil 9 of 10 and a Kimi K3 harness 0 of 10, confirmed by Scientific American on 2026-10-14 (article URL not recorded). ProofCouncil runs GPT-6 Astra Pro, GPT-6 Astra, Claude Fable 5.1, Claude Sonnet 5 and Gemini 3.1 Pro ([third batch](https://1stproof.org/third-batch.html)), so it is not independent of GPT-6 Astra. Figures for GPT-6 Astra alone (7 of 10; 4 of 10 with adequate citations) do not appear in public text and are unverified.
- **Overclaims and errors:**
  - A GPT-5 "Erdős breakthrough" post was deleted in October 2025.
  - The formal-conjectures "solved" tag on A6697 covers only the generating-function algebra.
  - Statements were misformalised (formal-conjectures issue #5226, A379240, #263).
  - cochon123's uniform Lemma F was wrong.
  - Mantovanelli's own v3 says his v2 finite-state closure "left a semantic gap".
  - Shallit's Cooper–Dutle paper had a gap in v1; a later model fixed it in v2.
  - D. Wachs ([arXiv 2609.22339](https://arxiv.org/abs/2609.22339)) showed that a step of Z.-W. Sun's Catalan claim ([arXiv 2609.04176](https://arxiv.org/abs/2609.04176)) does not justify the claimed estimate.
- **A positive data point:** OpenAI's ten proofs (2026-08-01) were audited by Sienicki & Sienicki ([arXiv 2608.14673](https://arxiv.org/abs/2608.14673), v3 2026-09-09) from 18 chapter reviews. No confirmed substantive error remains in a principal result; one chapter has a request for major revision. The draft wrongly called them unreviewed.
- **Kernel exploits:**
  - Lean issue #14484 was opened on 2026-07-22 by phulin. The report says it was "largely generated with AI" but names no model, so the draft's "found with GPT-5.6 Sol" is unverified. It was fixed in v4.32.1 (2026-07-22).
  - Issue #14576 ("Kernel accepts wrong-structure projections") was opened on 2026-07-28 after Ramana Kumar's AI-assisted Collatz "disproof" of 2026-07-25, which also used a separate nanoda bug, fixed a week earlier. #14576 was fixed in v4.32.2 (2026-07-28) ([postmortem](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)).
  - Our library and catalog pin v4.30.0. Toolchains v4.32.2, v4.34.0 and v4.35.0 (released 2026-10-12) are installed locally; replay under v4.35.0.
- **Rule 30 resolutions:** every claimed full resolution checked so far is invalid: Topal, Ulrey, azhar, Tan, Fradkin, Brauer, Basta, Deva, Das, and TLMC #1243.

---

## 2. Technique cards

### A. Irrationality and transcendence (base-B real, 2-adic, rationality over ℚ, natural boundary, transcendence)

#### A1. Stanley engine: P-recursive, or algebraic, with finitely many values ⇒ eventually periodic
*Promise: none as a route. Library value: medium (two forms not yet in the library). Verification: Formal (3rd party), CC0, not rebuilt. The author's Comparator configuration checks four headline theorems against the three standard axioms, with nanoda disabled; we did not run it.*
- **Origin.** Ralf Stephan (IGDORE) with Claude Code, [rwst/Ceiling-Orbits](https://github.com/rwst/Ceiling-Orbits), 2026-07-29 to 2026-09-07. Stanley's closure property became a proved theorem, instead of a cited axiom, on 2026-09-06. Paper: DOI [10.13140/RG.2.2.10727.82081](https://dx.doi.org/10.13140/RG.2.2.10727.82081). Classical input: R. P. Stanley, Eur. J. Combin. 1 (1980) 175–188.
- **AI.** Claude Code wrote the Lean under the author's direction and review. The mathematics is elementary or classical.
- **Proved.**
  - `RB.eventuallyPeriodic_of_isPRecursive`: a finite-range w : ℕ → ℚ satisfying a nontrivial recurrence Σ_j Q_j(n)·w(n+j) = 0 is eventually periodic.
  - `eventuallyPeriodic_of_isAlgebraic_of_finite_coeffs`, and `Stanley.pRecursive_of_isAlgebraic` over any field of characteristic 0.
  - The Comparator configuration lists `RB.Gen.not_isPRecursive_word`, `RB.not_isPRecursive_orbit`, `RB.Gen.not_isAlgebraic_wordSeries` and `RB.not_isAlgebraic_orbitSeries`: the parity words of ceiling orbits in rational bases are not P-recursive, and their series are not algebraic.
- **Forms.** `p-recursive` and `fatou`, both only stated in CATALOG.md. `rational-any-field` over ℚ is already proved: `problem1_iff_series_not_rational ℚ` in [LinearRelations.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/LinearRelations.lean).
- **Idea.** Past some N, every window recurs infinitely often, so Σ_j Q_j(t)·w(m+j) is a polynomial in t with infinitely many roots. Its top coefficients give a recurrence with constant coefficients, which on a finite alphabet is a finite-state map. Stanley's step: ℚ(X)(f) is a finite extension closed under d/dX, so f, f′, …, f^(d) are linearly dependent.
- **Transfer.** *Update 2026-10-17:* `p-recursive` no longer needs the port. The kit's [Holonomic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/Holonomic.lean) proves it with an elementary version of the idea below: recurring windows make Σ aᵢ pᵢ vanish identically. `fatou` still needs Stanley's step. The original plan: port the three Ceiling-Orbits files named below to prove `p-recursive` and `fatou`. This also proves, as a theorem, that holonomic tools (A9) cannot work on f = Σ c(t)zᵗ, because f is D-finite exactly when Problem 1 fails.
- **Obstacle.**
  - These are equivalences only.
  - The code targets Lean v4.33.0-rc1 (released 2026-07-15, before the kernel fixes in v4.32.1 and v4.32.2) and must be ported to v4.30.0.
  - Mathlib `c5ea003` lacks `PowerSeries.coeff_iterate_derivative` (confirmed). It does have the `DifferentialAlgebra` instance for finite intermediate fields that Stanley's step needs.
- **Artifacts.** CC0. Port only the **Ceiling-Orbits** copies of `RB/EventuallyPeriodic.lean` (about 24 KB), `CITED/StanleyProof.lean` (about 28 KB) and `CITED/Stanley.lean`. In Transcendence-Criteria, `CITED/Stanley.lean` is still `axiom pRecursive_of_isAlgebraic`, and that repository's `RB/EventuallyPeriodic.lean` imports it.

**Which of Stephan's CC0 files are axiom-free.** "Axiom-free" below means that a static scan of the file's import closure, within its repository, finds no `axiom` declaration. The audit ran this scan and this revision re-ran it; nothing was built. A file that imports axioms can still contain axiom-free theorems: two of the four Comparator-listed theorems live in `RB/GeneralBase.lean`. So run `#print axioms` on every ported theorem. Both repositories pin Lean v4.33.0-rc1; replay whatever is ported.

| Repository | File | Import closure | Use |
|---|---|---|---|
| Ceiling-Orbits | `RB/EventuallyPeriodic.lean` | axiom-free | Stanley engine (A1) |
| Ceiling-Orbits | `CITED/Stanley.lean`, `CITED/StanleyProof.lean` | axiom-free (proved 2026-09-06) | algebraic ⇒ P-recursive (A1) |
| Ceiling-Orbits | `RB/Rigidity.lean` | axiom-free | window–residue rigidity (A5) |
| Ceiling-Orbits | `RB/GeneralBase.lean` | **imports** `BertinPisot/SetSTU.lean`, which declares 8 axioms (e.g. `pow_mem_S`, `theorem_5_2_3`) | do not port as is |
| Transcendence-Criteria | `ForMathlib/RingTheory/PowerSeries/Rationality.lean`, `.../EventuallyPeriodic.lean` | axiom-free | Kronecker's criterion; rational ⇔ eventually periodic (B3) |
| Transcendence-Criteria | `ForMathlib/LinearAlgebra/Matrix/Hankel.lean`, `.../Determinant/AntiDiagonal.lean` | axiom-free | Hankel matrices (B3) |
| Transcendence-Criteria | `ForMathlib/Combinatorics/SubwordComplexity.lean`, `.../InfiniteComplexity.lean` | axiom-free | finite and infinite Morse–Hedlund (A5, B4) |
| Transcendence-Criteria | `CITED/AlloucheShallitComplexity.lean` | axiom-free | Cobham's linear bound, a theorem (B4) |
| Transcendence-Criteria | `L90/DivergentAperiodic.lean`, `L90/RationalCycles.lean` | axiom-free (this revision's re-run of the scan) | Lagarias's parity theorem (A6) |
| Transcendence-Criteria | `B3/DigitPeriodicity.lean` | **imports** `AB/StammeringSequences.lean` (axiom `isStammering_of_automatic`), `BL/Basic.lean` and `BL/ConjugacyMap.lean` | do not port; the 2-adic forms are re-derived in [TwoAdic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TwoAdic.lean) |
| Transcendence-Criteria | `BL/Basic.lean` | **declares** `axiom shiftAut_eq_id_or_V` (line 328) | do not port |
| Transcendence-Criteria | `RB/EventuallyPeriodic.lean`, `CITED/Stanley.lean` | `CITED/Stanley.lean` still declares `axiom pRecursive_of_isAlgebraic` | use the Ceiling-Orbits copies |
| Transcendence-Criteria | `AB/*`, `BL/ConjugacyMap.lean`, `CITED/AdamczewskiFaverjon*` (`lemme_2_2`, `lemma_2_8`), `CITED/SubspaceTheorem.lean`, `CITED/Ridout.lean`, `CITED/CorvajaZannierAlgebraic.lean`, `CITED/NairKumarRout.lean` | declare cited axioms | do not port |

#### A2. 2-adic presentations
*Promise: low. Library value: already realised in [TwoAdic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TwoAdic.lean). Verification: our library (second batch) for the 2-adic forms; Formal (3rd party) for Stephan's ℤ₂ digit lemma, which imports axioms; preprint or computed for the rest.*
- **Origin.**
  - Stephan with Claude Code, [rwst/Transcendence-Criteria](https://github.com/rwst/Transcendence-Criteria), 2026-07-18 to 2026-08-06: `B3.not_isEventuallyPeriodic_binaryDigit`, `B3.ratInt_eventuallyPeriodic_binaryDigit`.
  - N. Berzai's remark "the same object over ℤ₂" ([rule30-left-edge](https://github.com/nateberzai-svg/rule30-left-edge), September–October 2026).
  - placego [RULE30-PRIZE.md](https://github.com/ghywel/placego/blob/main/RULE30-PRIZE.md) §8.77, 2026-10-09.
  - [wryan2986/rule30-lab](https://github.com/wryan2986/rule30-lab), July–August 2026.
  - Z. Chen and A. Winterhof, [arXiv 2504.09933](https://arxiv.org/abs/2504.09933), 2025-04-14.
- **AI.** Claude Code (Stephan's Lean). Claude, for computation and editing (Berzai). Claude Cloud with a GPT audit, GC814 (placego). Not stated (wryan2986). None (Chen–Winterhof).
- **Proved.**
  - Lean (Stephan): the digits of v ∈ ℤ₂ are eventually periodic iff v ∈ ℚ.
  - In the frame of the right edge, R_{t+1} = R_t ⊕ (2R_t ∨ 4R_t) and c(t) = bit t of R_t (checked for t < 2000).
  - H(a) = a ⊕ (2a ∨ 4a) permutes ℤ/2^k for k ≤ 20. It is not ergodic, since H(0) = 0.
  - wryan2986: a unit-triangular isometry Δ such that eventual periodicity holds iff Δ(S) is rational.
  - Chen–Winterhof: an algebraic 2-adic integer of degree d ≥ 2 has N-th 2-adic complexity ≥ N/d + O(1). A sequence that is both 2-adic algebraic and automatic is eventually periodic.
- **Forms.** `two-adic` and `fcsr-complexity`, proved in [TwoAdic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TwoAdic.lean) (`problem1_iff_padic_irrational`, `problem1_iff_two_adic_complexity`, `problem1_iff_no_odd_fraction`). `nks-integer-rows` (stated in CATALOG.md) is the T-function reading.
- **Idea.** Read a row as a 2-adic integer. Rule 30 becomes a 1-Lipschitz T-function, and c(t) is digit t of Hᵗ(1).
- **Transfer.** Done for the library: TwoAdic.lean re-derives the 2-adic forms, so Stephan's `B3/DigitPeriodicity.lean` is not needed. The `nks-integer-rows` form remains.
- **Obstacle.**
  - The diagonal read digit_t(Hᵗ(1)) is exactly what ergodic results do not control. They control fixed digits, that is fixed diagonals, which are all eventually periodic.
  - Rule 90 (multiplication by 1 + y²) has the same presentation and an eventually constant centre (F-OR).
- **Artifacts.** `B3/DigitPeriodicity.lean` (CC0) is **not** axiom-free: it imports `AB/StammeringSequences.lean`, `BL/Basic.lean` and `BL/ConjugacyMap.lean`, all of which declare axioms (table in A1). wryan2986 is MIT and Berzai MPL-2.0; placego has no licence.

#### A3. Tail decay (Liouville, Erdős–Straus): reduction to unbounded runs
*Promise: low. Verification: Formal (3rd party) for #1051; preprint for #258.*
- **Origin.**
  - [Erdős #1051](https://www.erdosproblems.com/1051): Aletheia, Google DeepMind's agent built on Gemini Deep Think. Solved in December 2025 and made public on 2026-01-29/30; case study [arXiv 2601.22401](https://arxiv.org/abs/2601.22401).
  - Sharp generalisation by Barreto, Kang, Kim, Kovač and Zhang, [arXiv 2601.21442](https://arxiv.org/abs/2601.21442) (v1 2026-01-29, v3 2026-07-08; to appear in Bull. LMS).
  - Lean proofs by [Seed-Prover 1.5](https://github.com/ByteDance-Seed/Seed-Prover/blob/main/SeedProver-1.5/erdos_1051.lean), by K. Barreto, and in [LeanMarathon](https://arxiv.org/abs/2606.05400).
  - [Erdős #258](https://www.erdosproblems.com/258): P. Chojecki with GPT-5.4, using Theorem 1.1 of [Tao–Teräväinen](https://arxiv.org/abs/2512.01739). From 2026; the date 2026-04-14 in our survey is not confirmed, since the problem page gives none.
- **AI.**
  - Aletheia solved the original #1051 on its own. One of five human graders objected to an unjustified "standard comparison theorems" step.
  - The material beyond the original problem, including the golden-ratio threshold, "is largely a product of human-AI interactions" (abstract of 2601.21442). The draft's "humans proved the threshold" was wrong.
  - #258: Tao–Teräväinen credit "Przemek Chojecki using GPT 5.4 Thinking" (footnote to Remark 1.4); erdosproblems.com says GPT-5.4 Pro. The model noticed that an existing theorem settles the problem.
- **Proved.**
  - If a_n is strictly increasing and limsup a_n^(1/φⁿ) = ∞, then Σ 1/(a_n·a_{n+1}) is irrational. The threshold is sharp.
  - Σ τ(n)/(a₁⋯a_n) is irrational whenever a_n → ∞.
- **Forms.** `binary-irrational` and `base-b-irrational` ([BinaryIrrational.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/BinaryIrrational.lean)); the stronger statement "unbounded runs" and the form `return-words` (stated) in CATALOG.md.
- **Idea.** If S = P/Q, then Q·D_N·(S − S_N) is a positive integer for every N. Fast growth pushes it below 1 along a subsequence.
- **Transfer.**
  - For x = Σ c(t)·2^(−t−1) = a/q, every white run followed by a black cell is shorter than log₂ q + 1. Since no column is eventually constant, "c has runs of unbounded length" implies Problem 1.
  - Data: the record runs in 10⁷ bits are 22 (white) and 23 (black), about log₂ n.
  - Dibujaron's Lean bounds point the other way: a black run starting at time a ≥ 1 is shorter than a, and a white run is shorter than 3a.
- **Obstacle.**
  - 0/1 digits decay exactly geometrically, so the Liouville margin is zero.
  - "Unbounded runs" is a rare-pattern statement about one orbit, strictly stronger than Problem 1: words like Thue–Morse are aperiodic with bounded runs.
- **Artifacts.** `erdos_1051.lean` (Apache-2.0), LeanMarathon (Apache-2.0), formal-conjectures `1051.lean` and `258.lean` (Apache-2.0).

#### A4. Conspiracy repulsion and prime-pattern lattices: a "Chowla for c" target
*Promise: low. Verification: preprint (Tao–Teräväinen); Lean conditional on a conjecture (#251); announced (normality claims).*
- **Origin.**
  - T. Tao and J. Teräväinen, [arXiv 2512.01739](https://arxiv.org/abs/2512.01739) (v1 2025-12-01, v2 2026-04-25). The phrase "conspiracy repulsion" is Tao's, from a comment on V. Kovač's [erdosproblems.com blog post](https://www.erdosproblems.com/forum/thread/blog:4) (2026-02-02).
  - J. Land, Erdős #251, conditional on Kuperberg's uniform Hardy–Littlewood conjecture, 2026-09-05/06 ([beetree/math_erdos_251](https://github.com/beetree/math_erdos_251)).
  - Normality claims posted on 2026-09-07 are announcements only.
- **AI.** None in the Tao–Teräväinen proof: "the text in this paper is entirely human-generated", and ChatGPT wrote only plotting code. Land's Lean was written by about ten Gemini 3.8 Flash workers, coordinated and checked by Codex.
- **Proved.** Σ ω(n)/2ⁿ is irrational: Erdős #69, and #257 for the primes.
- **Forms.** `base-b-irrational`; Problem 2 (CATALOG.md, Problems 2 and 3); the stronger statement "disagreements of positive density" (vanishing autocorrelations).
- **Idea.**
  - Rationality puts every tail on a lattice (1/Q)ℤ.
  - A dilation identity, ω(pn) = ω(n) + 1 − 1_{p|n}, together with alternating Gowers-cube sums, cancels the leading terms.
  - Correlation estimates then spread the remainder, which contradicts the lattice.
- **Transfer.**
  - The argument needs (i) a dilation identity for c and (ii) two-point decorrelation of c at every shift.
  - (ii) alone already implies Problem 1, since a period h forces correlation 1 at shift h. So a "Chowla conjecture for c" is a natural target between Problems 1 and 2.
  - Problem 2 (density ½) does not imply Problem 1, whereas full normality does.
- **Obstacle.**
  - c has neither ingredient.
  - Rule 90 does have the dilation identity cell(2t, 2i) = cell(t, i), and its centre is eventually constant (F-OR).
  - The correlation input is as hard as Problem 2.
- **Artifacts.** Nothing reusable. formal-conjectures `69.lean` and `257.lean` (Apache-2.0); beetree has no licence.

#### A5. Window–residue rigidity with a growth ceiling (rational-base words)
*Promise: low. Verification: Formal (3rd party), CC0, not rebuilt. The rigidity files have axiom-free import closures; the paper's headline transcendence results rest on three cited axioms.*
- **Origin.**
  - Stephan with Claude Code, [arXiv 2609.19007](https://arxiv.org/abs/2609.19007) (v1 2026-07-18, v2 2026-09-17), in [Transcendence-Criteria](https://github.com/rwst/Transcendence-Criteria) and [Ceiling-Orbits](https://github.com/rwst/Ceiling-Orbits).
  - It formalises Akiyama–Frougny–Sakarovitch (Israel J. Math. 168, 2008) and Dubickas (Glasgow Math. J. 51, 2009).
  - Context: J. Kopra, [arXiv 2202.13809](https://arxiv.org/abs/2202.13809) (TCS 946, 2023).
- **AI.** The acknowledgements say the author "utilized Claude Code as an AI coding assistant to aid in the Lean 4 formalization". The aperiodicity mathematics is classical.
- **Proved.**
  - The parity word of x_{n+1} = ⌈3x_n/2⌉ is not eventually periodic, and its factor complexity is ≥ ⌊41(m−1)/24⌋ + 1.
  - The same holds for every coprime p > q ≥ 2.
  - Irrationality of K(3) stays open. The abstract says the headline transcendence results rest on "three cited axioms".
- **Forms.** `morse-hedlund` ([ShiftOrbit.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/ShiftOrbit.lean)); `eventual-word`; the stronger statement NumberLike, which is Kopra's setting.
- **Idea.**
  - A window of length m pins x_n modulo 2^m, so a repeated window costs a factor 2^k in |x_c − x_a|.
  - The state grows only like (3/2)^c, and log₂(3/2) < 1, so long repetitions are impossible.
- **Transfer.**
  - This is the Jen–Kopra width-2 theorem in disguise: left-permutivity plays the rigidity, and the light-cone edge plays the growth ceiling.
  - Width 1 needs one more relation that pins a neighbouring column from c. Masked Jen (F1) supplies it only at black times.
- **Obstacle.**
  - One column does not determine the left half, because the right half is free. So there is no entropy deficit like log₂(3/2) < 1.
  - Rules 90, 150 and 210 share every ingredient (F-OR).
- **Artifacts.** CC0.
  - `RB/Rigidity.lean` (axiom-free closure). `RB/GeneralBase.lean` imports `BertinPisot/SetSTU.lean`, which declares 8 axioms.
  - In Transcendence-Criteria: `ForMathlib/Combinatorics/SubwordComplexity.lean`, a finite Morse–Hedlund (complexity ≤ n on a window of length ≥ 3n forces a long periodic factor), useful for window certificates like our `Rule30FactorWindow`; and `InfiniteComplexity.lean` (B4). Both have axiom-free closures.

#### A6. Exact 2-adic arithmetic decoding (valuation traps, closed forms, linear forms in logarithms)
*Promise: low. Verification: mixed, as listed under Proved.*
- **Origin.**
  - Lagarias, Acta Arith. 56 (1990), Cor. 2.1b, formalised by Stephan with Claude Code (`L90/*.lean` in [Transcendence-Criteria](https://github.com/rwst/Transcendence-Criteria), July–August 2026).
  - [rwst/Antihydra-Basics](https://github.com/rwst/Antihydra-Basics), 2026-03-08 to 2026-03-25.
  - BMO 3: Lean with Aristotle (2026-04-01); Rocq file [BMO3.v](https://github.com/ccz181078/busycoq/blob/BB6/verify/BMO3.v) by mxdys.
  - BB(6) holdout [1RB1LA_1RC1RE_…](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---): Lean statement of 2026-04-12 in rwst/bbchallenge.
- **AI.** The Antihydra-Basics README says "the Lean proofs are all by frontier LLMs, mostly Opus-4.6", with plans by Gemini 3.1 and Opus 4.6. BMO 3: Aristotle for the Lean, unnamed LLMs for the Rocq. BB(6) holdout: number theory by Pomme, Lean by Claude Opus 4.6 and Aristotle.
- **Proved.**
  - Lean (Lagarias): an eventually periodic parity sequence forces a finite 3x+1 orbit. The `L90` files have axiom-free import closures.
  - Lean (Antihydra-Basics): orbits of ⌈3n/2⌉ are not eventually periodic mod 2^N, with no sorry. The same repository leaves K(3,7) as sorry and states a false lemma, `M_1_3_co_null`.
  - Lean and Rocq (BMO 3): the recurrence never hits a power of 4.
  - Conditional: the BB(6) holdout never halts, given an axiomatised Baker–Wüstholz bound. An axiom-free version (September 2026) is only announced.
- **Forms.** `two-adic`; `eventual-word`; the constrained-orbit shape of Q01 and Absorption.
- **Idea.** Decode the state as an integer whose dynamics is exactly 2-adically expanding or affine, then let 2-adic valuations contradict periodicity.
- **Transfer.** Run on x_M and x_{M+P}, the Antihydra argument reproduces Condrey's time-shift defect identity, which is masked Jen (F1). It still needs column 1 to be eventually periodic at the white times.
- **Obstacle.**
  - Rule 30 is not affine over ℤ, because of the OR.
  - Near the right edge its diagonal dynamics is an isometry (an odometer), not a contraction.
  - c has no closed form, and Baker–Wüstholz is not in Mathlib.
- **Artifacts.** CC0 (rwst repositories); MIT (ccz181078/busycoq, BB6 branch).

#### A7. Natural boundary and D-finite dichotomies
*Promise: low. Library value: low to medium (the `natural-boundary` form). Verification: peer-reviewed; the bivariate corollary is derived (words survey) and unchecked.*
- **Origin.** Bell, Chen, Nguyen and Zannier, [arXiv 2306.02590](https://arxiv.org/abs/2306.02590) (2023-06-05; Math. Z. 2024). Classical inputs: Szegő (1922); Pólya–Carlson (F. Carlson, Math. Z. 9, 1921); Lipshitz, J. Algebra 113 (1988).
- **AI.** None.
- **Proved.** A D-finite series whose algebraic-integer coefficients have height o(n₁ + … + n_m) is rational, with cyclotomic-monomial denominators.
- **Forms.** `natural-boundary` (stated in CATALOG.md); `p-recursive`.
- **Idea.** A power series with finitely many distinct coefficients is either rational or has the unit circle as its natural boundary (Szegő).
- **Transfer.**
  - Equivalence: Problem 1 holds iff the unit circle is a natural boundary of Σ c(t)zᵗ.
  - Derived corollary: the bivariate space–time series Σ cell(t, q−t)·xᵗ·y^q is not D-finite. Otherwise every column, as a diagonal, would be D-finite, hence rational, hence eventually periodic, contradicting Jen.
- **Obstacle.**
  - Szegő and Pólya–Carlson are formalised nowhere we found; A1 is far cheaper.
  - The bivariate corollary uses only Jen, so it also holds for rules 90, 150 and 210 (F-OR).
- **Artifacts.** Papers only.

#### A8. Hasse derivatives and iterative differential Galois theory
*Promise: low. Verification: peer-reviewed.*
- **Origin.** J. Kramer-Miller, [arXiv 2404.06968](https://arxiv.org/abs/2404.06968) (2024-04-10); Algebra & Number Theory 20 (2026) 1597–1614.
- **AI.** None.
- **Proved.** The Artin–Hasse exponential mod p is transcendental over F_p(x).
- **Forms.** `cobham-christol` (transcendence over F₂(x), a stronger statement); `series-f2-lfsr`.
- **Idea.** For a series algebraic over F_p(x), all higher logarithmic (Hasse) derivatives lie in one finite extension. The proof shows that they climb an infinite filtration instead.
- **Transfer.** An untried bridge. Mod 2, Hasse derivatives act through Lucas' theorem: C(n,k) is odd iff k ⊆ n bitwise. This matches the support formula c(t) = #{r ∈ S_{t+1} : r ⊆ t} mod 2 (B2), whose sets S_m obey a nonlinear OR-convolution recursion that rules 90 and 150 lack.
- **Obstacle.** The method needs a functional equation for Σ c(t)xᵗ, and none is known. Transcendence over F₂(x) is also stronger than Problem 1.
- **Artifacts.** Paper only.

#### A9. Closed for Problem 1: methods that need structure c does not have

| Technique, origin, date and URL | AI | Status | Forms | Why it cannot reach Problem 1 |
|---|---|---|---|---|
| Mahler's method in several variables: Adamczewski–Faverjon, Annals ([arXiv 2012.08283](https://arxiv.org/abs/2012.08283); addendum [2407.18578](https://arxiv.org/abs/2407.18578), 2024). Lean in rwst/Transcendence-Criteria (July–August 2026), modulo `AF.lemme_2_2` and `AF.lemma_2_8`. | Claude Code (Lean) | peer-reviewed; Lean with 2 cited axioms | `cobham-christol`, `base-b-irrational` | The dichotomy "rational or transcendental" says nothing about the rational case, which is Problem 1. It also needs a Mahler equation, which c lacks. |
| Stammering sequences and the Subspace Theorem: Adamczewski–Bugeaud (Annals 165, 2007); Stephan, [arXiv 2607.11648](https://arxiv.org/abs/2607.11648) (2026-07-13) and arXiv 2609.19007 (Theorems B, C); Lean in [Transcendence-Criteria](https://github.com/rwst/Transcendence-Criteria). The formalisation refuted Nair–Kumar–Rout ([arXiv 2506.02898](https://arxiv.org/abs/2506.02898)) Theorem 1.3(i): `NKR.thm13i_unrepaired_false`, in `CITED/NairKumarRout*.lean` of Transcendence-Criteria (not in Subspace-Theorems). | Claude Code | preprint; Subspace Theorem as a cited axiom | `base-b-irrational`, `morse-hedlund` | In base 2 with digits {0,1}, rational already means eventually periodic. These methods only separate algebraic irrationals from transcendentals. |
| Subspace-Theorems roadmap: [rwst/Subspace-Theorems](https://github.com/rwst/Subspace-Theorems) (**Apache-2.0**, not CC0; created 2026-09-15, pushed 2026-10-13; Lean v4.35.0-rc3). It reports Roth over number fields, Ridout, the p-adic form, the two-variable Subspace Theorem and Mahler's theorem on (p/q)^k as landed, sorry-free and on standard axioms; the full Subspace Theorem is still open. Not rebuilt by us. | AIs implement under Tau Ceti's "AIs-welcome" rules | formal (3rd party), not rebuilt | `base-b-irrational` | Same reason as the row above. The draft's "useful only once Roth lands" is outdated: Roth is reported landed, and it still does not help. |
| Arithmetic holonomy bounds: Calegari–Dimitrov–Tang ([arXiv 2408.15403](https://arxiv.org/abs/2408.15403), 2024-08-27; [2510.04156](https://arxiv.org/abs/2510.04156), 2025-10-05) | none | preprint | `natural-boundary`, `two-adic` | Needs continuation beyond conformal size 1, and f extends past the unit circle iff Problem 1 fails. |
| Determinant and interpolation methods: [openai/math](https://github.com/openai/math) (released 2026-10-06; 719 manuscripts) claims that Catalan's constant is irrational and that μ(π) = 2, with Lean and standard-axiom Comparator configurations at v4.34.1, not replayed by us. Liu–Jiang–Zhang claim μ(log r) = 2 ([arXiv 2610.10192](https://arxiv.org/abs/2610.10192), 2026-10-07, no Lean). A competing Catalan claim by Z.-W. Sun ([arXiv 2609.04176](https://arxiv.org/abs/2609.04176), 2026-09-03; no AI disclosure in the abstract) has a gap found by D. Wachs ([arXiv 2609.22339](https://arxiv.org/abs/2609.22339), 2026-09-16). | model-produced (openai/math); none disclosed by Liu–Jiang–Zhang | formal claim, unreviewed | `base-b-irrational` | The target must be a period or come from the exponential map; x has no integral representation. The audit found no cellular-automaton, automatic-sequence or digit result in openai/math that transfers. |
| Parameter displacement: Bai, μ(π) ≤ 7.10186… ([arXiv 2609.11276](https://arxiv.org/abs/2609.11276), 2026-09-10); Niedbala, μ(ζ(3)) < 5.51388 ([arXiv 2609.26980](https://arxiv.org/abs/2609.26980), 2026-09-22) | GPT-5.6 Sol and GPT-6 Astra (Bai); Claude (Niedbala) | preprint | `dirichlet-liouville` | Needs an existing family of constructions for the constant. |
| Ramanujan Machine and conservative matrix fields: Kaminer group (PNAS 2024; [arXiv 2502.17533](https://arxiv.org/abs/2502.17533); [2507.08138](https://arxiv.org/abs/2507.08138)) | search plus LLM harvesting of formulas | peer-reviewed | `base-b-irrational` | Needs a holonomic representation, which exists iff Problem 1 fails (A1). |
| Lean transcendence infrastructure: ζ(3) ([arXiv 2503.07625](https://arxiv.org/abs/2503.07625)); Gelfond–Schneider ([arXiv 2603.24823](https://arxiv.org/abs/2603.24823), 2026-03-25); Subspace-Theorems (row above) | none for the first two | formal | `fatou` | Specific constants only. The missing piece for our forms is a functional equation for c, not Roth. |
| Digit-set density thinning: [Erdős #125](https://www.erdosproblems.com/125), AlphaProof Nexus (2026-03-30) | autonomous | formal | `base-b-irrational` | Needs exact self-similarity. Rule 90 has it and is periodic (F-OR). |
| Kummer/Lucas carry counting: Erdős #728/#729 (2026-01; [arXiv 2601.07421](https://arxiv.org/abs/2601.07421)) | GPT-5.2 Pro and Aristotle | formal | `cobham-christol` | Proves statements of the form "some n exists"; cannot exclude all periods. Lucas structure is shared with rule 90. |
| Equivalences plus finite exclusions for Erdős irrationality problems: Plectis ([wcook04/plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), Apache-2.0; 2026-09-01 to 2026-10-15) | AI agents; the author has not verified every claim | preprint with Lean statements | `hankel`, `base-b-irrational` | Contains no cellular-automaton content. Useful as a template for a Comparator-backed claims registry. It pins v4.30.0, as our library does. |

### B. Power series over F₂, linear complexity, automaticity

#### B1. Duhamel decomposition and Cartier closure of the 2-kernel
*Promise: low; a long shot, gated by two controls (the draft rated it medium). Verification: preprint; the identity was checked here for t ≤ 160.*
- **Origin.**
  - N. Berzai, [rule30-left-edge](https://github.com/nateberzai-svg/rule30-left-edge), Part II: paper of 2026-09-16, revised 2026-09-24 and in October.
  - The same forcing identity appears in rule30-foundry's [CLAIM_LEDGER](https://github.com/Patto1155/rule30-foundry/blob/main/docs/CLAIM_LEDGER.md) and in our archive's notes on the algebraic normal form.
- **AI.** "Computational and editorial assistance from Claude" (Berzai). Codex and Claude agents (foundry).
- **Proved.**
  - U_{t+1} = ΛU_t + Q_t, with Λ = z + 1 + z⁻¹ (rule 150) and Q_t = Σ_x u_x·u_{x+1}·z^x (the quadratic source).
  - Hence c_t = 1 + Σ_{s<t} Σ_x T_{t−1−s}(x)·u^s_x·u^s_{x+1}, where T_m is the rule-150 propagator and T_m(0) = 1.
  - The class of such functionals is closed under the Cartier operators Λ₀ and Λ₁, because Λ(z)² = Λ(z²) in characteristic 2. So the 2-kernel of c is the image of an explicit orbit.
  - deg F_t = 2t − 1, with a unique top monomial.
  - Certified negatives: no Mahler relation of depth ≤ 12 and degree ≤ 8000; a census of ≥ 138,672 distinct truncations. The census route is provably closed.
- **Forms.** `cobham-christol` (non-automaticity, equivalently transcendence over F₂(x): a stronger statement in CATALOG.md); `series-f2-lfsr` ([PowerSeriesF2.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/PowerSeriesF2.lean)).
- **Idea.** Rule 30 is rule 150 driven by the quadratic source, which is exactly the nonlinearity of the OR. Decimating by 2 maps the Duhamel class to itself, so non-automaticity is equivalent to the Cartier orbit being infinite.
- **Transfer.** Two routes:
  - find an invariant of the chiral Cartier recursion that takes infinitely many values; or
  - find an Allouche–Shallit–Yassawi family: one residue class per level, with pairwise distinct kernel elements.

  Either makes Σ c(t)xᵗ transcendental over F₂(x), and so proves Problem 1. Any candidate must first pass two controls:
  - **Rule 54.** Rule 54 = rule 150 ⊕ (l ∧ r) has the same propagator, a quadratic source and the same Cartier closure, which uses only Λ(z)² = Λ(z²). Yet its single-seed centre is (1100)^∞ (computed for t < 400 by the audit and again here; Berzai Part V also lists it as period 4). Rule 22 = rule 150 ⊕ (l ∧ c ∧ r) has centre 1, 1, 0, 0, …. So an invariant must detect the chirality of the source; Berzai notes that "only the centre line and the chiral part of the source are visible to c".
  - **F-FIN.** c7, an infinite configuration with an alternating centre, satisfies the same Duhamel recursion. So the invariant must use the finite support of the seed row.
- **Obstacle.**
  - The target is strictly stronger than Problem 1: Thue–Morse is automatic and aperiodic.
  - No such invariant is known, and no finite census decides the question, since every finite word extends to an automatic sequence.
  - The source vanishes for linear rules, so the route passes the rule-90 firewall by construction. That is necessary but not sufficient, as rule 54 shows. The local, strip and DFA barriers do not apply.
- **Artifacts.** Berzai's paper (MPL-2.0). Our identity check, `duhamel_check.py` (scratch path in Appendix A).

#### B2. Lucas/Newton-support calculus and finite automaticity bounds
*Promise: low. Verification: preprint; support facts checked numerically by us for m ≤ 24.*
- **Origin.**
  - T. Nersissian, [arXiv 2609.25077](https://arxiv.org/abs/2609.25077) and [2609.25078](https://arxiv.org/abs/2609.25078) (v1 2026-09-18), and Zenodo [22747521](https://zenodo.org/records/22747521), [22747649](https://zenodo.org/records/22747649), [22747739](https://zenodo.org/records/22747739) (2026-09-14) and [18921456](https://zenodo.org/records/18921456) (2026-03-09).
  - D. Fomin, Zenodo [22646809](https://zenodo.org/records/22646809) (v6 2026-09-07).
  - Certified state bounds: Amat–Ganty–Mansutti (ASE 2025); Rowland–Yassawi ([arXiv 2408.00750](https://arxiv.org/abs/2408.00750)).
- **AI.** Not stated in Nersissian's papers. Fomin's bundle contains multi-agent "assault" memos, labelled as not adversarially checked; the papers state no AI use.
- **Proved.**
  - S_m = Inc(S_{m−1} Δ S_{m−2} Δ (S_{m−1} ⊛ S_{m−2})), where ⊛ is OR-convolution.
  - min S_m = ⌊m/2⌋ and max S_m ≤ F_{m+1} − 1, so the right-diagonal periods are unbounded. That unboundedness is older: Gravner and Griffeath, Theoret. Comput. Sci. 466 (2012) 64–86, Prop. 3.3, show that a left-permutive edge cellular automaton has no periodic solution, and state it for rule 30. Berzai cites it; Nersissian and Berzai Part III re-derive it.
  - Any 2-DFAO generating c needs ≥ 8,191 states reading the least-significant digit first, and ≥ 12,950 reading the most-significant digit first.
  - Fomin: c(t) = #{r ∈ S_{t+1} : r ⊆ t} mod 2. This refutes c(t) = [t ∈ S_{t+1}] from arXiv 2604.00165 (agreement 21/35).
  - Fomin's support wave: the front moves at speed exactly ½ and is generated by a finite automaton. Density statements reduce to a square-root discrepancy bound for one orbit.
- **Forms.** `cobham-christol` (finite-state lower bounds); `series-f2-lfsr`; `rational-any-field` (Nersissian's integer layers); Problem 2 (Fomin).
- **Idea.** Lift the diagonals to ℤ in the binomial (Lucas) basis: XOR becomes symmetric difference, and AND becomes OR-convolution of supports.
- **Transfer.** This gives an exact formula for c(t), and a possible source for the "unbounded family of distinguishable continuations" that non-automaticity needs. It connects to A8.
- **Obstacle.**
  - Every statement about the centre is finite.
  - Diagonal-period unboundedness also holds for rule 90's Pascal diagonals (F-OR).
  - |S₄₄| = 64,939, so the supports are as complex as the automaton itself.
- **Artifacts.** arXiv TeX and the Zenodo U-series (CC BY 4.0); Zenodo 18921456 (CC BY-NC-SA 4.0); Fomin's code (MIT) and papers (CC BY 4.0).

#### B3. Kronecker–Hankel criterion and number walls
*Promise: low as a route. Library value: realised in [LinearRelations.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/LinearRelations.lean). Verification: our library (second batch) for the Hankel forms; Formal (3rd party, not rebuilt, axiom-free closure) for Stephan's Kronecker; preprint for the number wall.*
- **Origin.**
  - Stephan with Claude Code, [rwst/Transcendence-Criteria](https://github.com/rwst/Transcendence-Criteria) (2026-07-18 to 2026-08-06): `isRationalSeries_iff_kroneckerDet_eventually_zero` over integral domains, and `isRationalSeries_iff_isEventuallyPeriodic_coeff`.
  - C. de Souza Cavalcante, Zenodo [21728308](https://zenodo.org/records/21728308) and [22253667](https://zenodo.org/records/22253667) (2026-07-31 and 2026-09-02), answering Shallit's Open Problem 8. Lunnon had already asserted the zero-free wall in OEIS [A301850](https://oeis.org/A301850) in 2018; the paper claims the certificate, the verifier and the lift to the reals.
- **AI.** Claude Code (Stephan's Lean). Cavalcante: "ChatGPT/Codex was used substantially."
- **Proved.**
  - Kronecker: over an integral domain, a power series is rational iff its Hankel determinants vanish for all large n.
  - Cavalcante: every entry in the rows m ≥ 0 of the number wall of a Dakota-based sequence over F₉ is nonzero; a lift gives a 3-valued real sequence with all shifted Hankel determinants nonzero.
- **Forms.** `hankel` and `rational-any-field`, proved in [LinearRelations.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/LinearRelations.lean): `problem1_iff_hankel_det` over any field, `problem1_iff_hankel_det_zmod_two`, `problem1_iff_hankel_det_int`, `problem1_iff_hankel_det_odd`, `problem1_iff_hankel_rank_unbounded`.
- **Idea.**
  - Kronecker: a singular Hankel matrix yields a recurrence, which a block-determinant identity propagates.
  - Number walls: the Desnanot–Jacobi recurrence turns the wall of an automatic input into a 2-D substitution tiling, which can be checked finitely.
- **Transfer.**
  - Done for the library: our LinearRelations.lean re-derives Kronecker's criterion over any field, so Stephan's files are a cross-check rather than a port.
  - Equivalent form: the F₂ number wall of c has no infinite zero window.
  - Data: L(c[0..16384)) = 8192 with max |L_n − ⌊(n+1)/2⌋| = 6, and the partial-quotient degrees follow the 2^(−k) law of a random sequence.
- **Obstacle.** A wall certificate exists only for automatic inputs, and c is not automatic (B2).
- **Artifacts.** CC0 Lean with axiom-free closures: `Rationality.lean` (about 34 KB), `EventuallyPeriodic.lean`, `Hankel.lean`, `AntiDiagonal.lean`. Cavalcante's verifier archive (CC BY 4.0), not run by us.

#### B4. Automaticity infrastructure
*Promise: low. Library value: low to medium. Verification: formal (various).*
- **Origin and AI.**
  - [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind; Apache-2.0). [Rule30.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/Rule30.lean) was added on 2026-09-07 and restated on 2026-10-14 without `answer(·)` (formal-conjectures #6762). The statements are human-written.
  - Sheng's verified automata: CMU MS thesis (May 2025), [Aeacu2/Automata](https://github.com/Aeacu2/Automata) (MIT, Lean 4.23). No AI reported.
  - Stephan with Claude Code: Cobham's bound and an infinite Morse–Hedlund in [rwst/Transcendence-Criteria](https://github.com/rwst/Transcendence-Criteria) (July–August 2026, CC0).
- **Proved.**
  - formal-conjectures: `IsAutomatic k a` means the k-kernel is finite; also `IsAutomaticInBase` and `NormalNumber.digitSeq`. Problem 1 now reads ¬∃ p > 0, ∃ N, ∀ t ≥ N, c(t+p) = c(t).
  - Sheng: an executable DFA/NFA/DFAO library with verified automata and DFAO pumping lemmas. It uses `rfl'` and `native_decide`, which our policy rejects.
  - Stephan: `AS.complexity_linear_of_automatic` (Cobham's linear-complexity bound, a theorem, in `CITED/AlloucheShallitComplexity.lean`).
  - Stephan: `ForMathlib/Combinatorics/InfiniteComplexity.lean` proves `pComplexity_lt_succ_of_not_isEventuallyPeriodic` (p(k) < p(k+1) for every word that is not eventually periodic, hence p(n) ≥ n + 1) and `exists_leftSpecial_of_not_isEventuallyPeriodic`. **The draft's claim that our `ShiftOrbit.lean` is the only Lean Morse–Hedlund was wrong.**
- **Forms.** `fc-bridge`: our library matches the restated formal-conjectures statement verbatim (`problem1_iff_fc` in [TransformsSeeds.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TransformsSeeds.lean)). `morse-hedlund` ([ShiftOrbit.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/ShiftOrbit.lean)); `special-factors` (`problem1_iff_right_special` in [WordsAutomata.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/WordsAutomata.lean)); `cobham-christol`.
- **Idea.** Superlinear factor complexity ⇒ not automatic ⇒ (Christol) transcendental over F₂(x).
- **Transfer.** Cross-check ShiftOrbit.lean against Stephan's InfiniteComplexity.lean. Left-special factors of every length follow from non-periodicity, but the converse fails (01^∞ has them), so that direction is not a new equivalent form.
- **Obstacle.** We found no formalisation of Christol's theorem, the full Cobham theorem or Sturmian theory.
- **Artifacts.** formal-conjectures (Apache-2.0); Aeacu2/Automata (MIT); Stephan's files (CC0, axiom-free closures).

#### B5. Controls every argument must pass
*Promise: none as a proof; these are mandatory calibrations. Verification: computed, and preprint.*
- **Origin.** Berzai, Parts III and V and the closed-routes table of [rule30-left-edge](https://github.com/nateberzai-svg/rule30-left-edge) (2026-09-16 to October; Claude-assisted); E. Chan-López and A. Martín-Ruiz, [arXiv 2604.00165](https://arxiv.org/abs/2604.00165) (v1 2026-03-31, v3 2026-09-06; AI use not stated); our survey and audit scripts (2026-10-15).
- **AI.** Claude for Berzai's computations; our checks were written by Claude Code agents.
- **Proved or computed.**
  - **Rule 126.** Its single-seed centre equals the Fredholm–Rueppel sequence (1 exactly at t = 2^k − 1) for t ≤ 2^14 (survey script, 0 mismatches), and it has a perfect linear-complexity profile. A perfect profile is therefore evidence of nothing.
  - **Rules 22 and 54.** Their centres are eventually periodic: rule 22 reads 1, 1, 0, 0, … (closed form in arXiv 2604.00165), and rule 54 reads (1100)^∞ (checked here for t < 400). Yet rule 22 has maximal ANF degree, and both have a prediction-matrix rank comparable to or larger than rule 30's, so degree and rank routes are closed (Berzai Part V). Rule 54 is also the control for the Duhamel–Cartier route (B1).
  - **Rule 60.** τ_d = d + 1 and a constant centre: Conjecture H decides nothing.
  - **Rules 90, 150 and 210:** the F-OR barrier.
  - **Rule 210:** see D5.
  - **The A₅ result.** Berzai's window transformation monoid contains A₅, so it is not solvable. This bounds nothing about the cost of computing one column.
- **Forms.** All forms; each control kills a class of arguments.
- **Idea.** Run every proposed argument on a rule whose answer is known.
- **Transfer.** Make each control a test in any new search or proof attempt.
- **Obstacle.** None; controls only rule things out.
- **Artifacts.** Berzai (MPL-2.0); arXiv 2604.00165; our scripts (Appendix A).

### C. Factor complexity, words, per-word exclusion, and Problems 2–3

#### C1. Word-exclusion engines: a finite right strip, then (masked) Jen
*Promise: medium for partial results; none for words of length 2–7. Verification: preprint (Berzai, placego), partly reproduced; Lean (ours).*
- **Origin.**
  - The method (strip, recurrent components, then Jen–Kopra) was first posted as a target by C. A. H. Ikram, OSF Preprints, 2026-05-15 ([osf.io/kybmz](https://osf.io/kybmz)).
  - **(a)** Berzai's K-window interface automaton, Part I of [rule30-left-edge](https://github.com/nateberzai-svg/rule30-left-edge) (2026-09-16 to October).
  - **(b)** Strip graphs and stable sets: proposed in the agent-run [cochon123/rule30-prize](https://github.com/cochon123/rule30-prize) (2026-09-10 to 2026-10-06), whose uniform Lemma F was wrong; repaired in [placego PROOFS.md](https://github.com/ghywel/placego/blob/main/PROOFS.md) entries 38, 40 and 41 (2026-10-09/10).
  - **(c)** Our strip and rank certificates (2026-10-15).
- **AI.** Claude (Berzai). cochon123 is run by an agent. placego: GPT repaired the uniform step (GC806) and Claude re-implemented the finite cases from the specification alone. Ours: Claude Code agents.
- **Proved.**
  - (a) Berzai excludes, for every number-like configuration:
    - 1^b 0^a for b ≥ 9;
    - 1^b v for b ≥ 29 and |v| ≤ 12;
    - 0^m 11 for m = 6 and m ≥ 8;
    - words with isolated 1s and zero-runs ≥ 10;
    - 1 0^9; 1^7 0 (K = 10); 0^7 1 (K = 12);
    - necklaces whose cyclic zero-runs are all ≥ 19 (family certificate not re-checked).

    A boundary theorem says the method works exactly for words w whose interface language L(w) contains only eventually periodic members.
  - (b) placego excludes, for every nonzero finite configuration: 0 1^q for q = 7 or q ≥ 9; 1 0^q for q ≥ 10; 24 words of period 10–14 and 115 of period 15–18.
  - (c) Ours: `Cert.sound` and `problem1_iff_no_word`, with 33 kernel-checked words of length 8–13 and about 180 more certified by two programs.
- **Verification details.**
  - (a): our re-implementation confirmed that 1^8 0 is uncertified at K = 10, 00000011 is certified at K = 10, and 0^7 1 is certified at K = 12.
  - (b): the finite parts were reproduced.
  - The engines are complementary: our e-forcing generator `certgen.py` finds no certificate for 0^7 1 at K ≤ 12, while Berzai's engine certifies it at K = 12.
- **Forms.** `eventual-word`, word by word (`problem1_iff_no_word` and `problem1_iff_no_primitive_word` in [WordsAutomata.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/WordsAutomata.lean); the core catalog's `Rule30StripCertificates.problem1_iff_no_word`). Each exclusion is a word-by-word case of the stronger statements NumberLike (Berzai) or FinConf (placego).
- **Idea.** Assume column 0 is eventually w^∞ and make the far right of the strip a free input. If every recurrent strongly connected component forces column 1 at the white letters of w to be eventually periodic, masked Jen finishes the proof.
- **Transfer.** Grow the excluded set mechanically (all primitive words of period 8–20), cross-certify with all three engines, and port the results as packed-Nat kernel certificates (S3).
- **Obstacle.**
  - Words are handled one at a time.
  - No primitive word of length ≤ 7 is certified at K ≤ 12 (Berzai) or width ≤ 16 (ours), and length 9 also fails at width ≤ 16. This is the computed local obstruction of §0.5: each strip graph has a component with two cycles whose white-phase outputs do not commute, and Lean's `word_lemma` turns such cycles into an aperiodic path.
- **Artifacts.** Berzai: MPL-2.0. placego and cochon123: no licence (placego's Lean probes are in `tests/probes/lean`). Ours: [research/generalize-jen/](research/generalize-jen/) (`strip_scan.py`, `certgen.py`) and [Rule30StripCertificates.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30StripCertificates.lean).

#### C2. Zero-entropy interface exclusions beside a period-2 centre
*Promise: low. Verification: preprint, second-read only within the project.*
- **Origin.** placego Theorems E, E″, Corollary F and A⁗, 2026-10-05 to 2026-10-07 ([RULE30-PRIZE.md](https://github.com/ghywel/placego/blob/main/RULE30-PRIZE.md) §8.57–8.59; PROOFS.md entries 11–15).
- **AI.** Claude (Local) proofs; GPT extensions and second reads.
- **Proved.**
  - If column 1 beside 0101 is Sturmian, the left half is never finite.
  - Rotation codings with infinitely many partial quotients above 2^(r+1) are excluded, so almost every rotation is.
  - Near-squares at unbounded periods are fatal, which covers period-doubling, Chacon and double-letter substitution fixed points.
  - Thue–Morse and paperfolding are excluded for left edges ≤ 15,868.
  - Computed: the real column 1 beside 0101 is "the wheel", a coding of rotation by 17/56 kicked by domain walls.
- **Forms.** `eventual-word` for the word 01, through Q01 and LR.
- **Idea.** A zero-entropy interface has long near-repetitions, and Jen-type arguments turn those into a contradiction with a finite left half.
- **Transfer.** None beyond the excluded classes.
- **Obstacle.** Every excluded class has zero entropy. The real output has positive entropy, about 0.08 bits per visible bit (measured).
- **Artifacts.** placego (no licence).

#### C3. Reflection complexity
*Promise: low. Library value: low (a cheap new form). Verification: preprint; the audit confirmed the statements of Cor. 42 and Thm. 41(b).*
- **Origin.** Allouche, Campbell, Li, Shallit and Stipulanti, [arXiv 2406.09302](https://arxiv.org/abs/2406.09302) (v1 2024-06-13, v4 2025-05-06).
- **AI.** None; Walnut computes reflection complexity for automatic sequences.
- **Proved.** x is eventually periodic iff r_x(n) ≤ ⌊(n+1)/2⌋ for some n ≥ 1, where r_x(n) counts length-n factors up to reversal. Otherwise r_x(n) ≥ 1 + ⌊(n+1)/2⌋, with equality iff x is Sturmian.
- **Forms.** A new form, not yet in CATALOG.md: Problem 1 holds iff r_c(n) ≥ 1 + ⌊(n+1)/2⌋ for all n ≥ 1. It would build on `morse-hedlund` in [ShiftOrbit.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/ShiftOrbit.lean).
- **Idea.** A Morse–Hedlund bound for factors counted up to reversal.
- **Transfer.** Add it to CATALOG.md and prove it with the ShiftOrbit machinery.
- **Obstacle.** It restates the same difficulty.
- **Artifacts.** The arXiv source with Walnut scripts; licence not checked.

#### C4. Guess an automaton, then verify it (LLM with Walnut; L*-learned invariants)
*Promise: medium for traps, word families and negative controls; none for c itself. Verification: unverified (diary); peer-reviewed (L*).*
- **Origin.**
  - J. Shallit's [Walnut Diary](https://cs.uwaterloo.ca/~shallit/diary.html), 2026-08-07 to 2026-08-11, with [Walnut](https://github.com/Walnut-Theorem-Prover/Walnut).
  - Khodier, Schaeffer and Shallit, [arXiv 2507.19717](https://arxiv.org/abs/2507.19717) (2025-07-25; CIAA 2025): automata learned with L* and certified by inductive conditions.
  - Guess-then-verify papers: [arXiv 2501.00784](https://arxiv.org/abs/2501.00784) (2025-01-01), [2506.13337](https://arxiv.org/abs/2506.13337) (2025-06-16), [2503.04122](https://arxiv.org/abs/2503.04122) (2025-03-06).
- **AI.** ChatGPT 5.6 and 5.6 Pro proposed morphic constructions, and Walnut proved them ("The construction is from ChatGPT, the proof is from Walnut"). Not re-run by us. L* is classical active learning, not an LLM.
- **Proved.** The diary reports cubefree and overlap-free words with prescribed curling sequences, and that no infinite ternary overlap-free word has an overlap-free curling sequence. Khodier et al.: correctness of a learned automaton for a "self-verifying" predicate follows from a few inductive conditions.
- **Forms.** `cobham-christol` (automatic objects only); traps for Absorption; negative controls for every form.
- **Idea.** Let a learner or a model guess a finite automaton; let a decision procedure check it.
- **Transfer.**
  - (a) Learn minimal traps or invariants of driven half-systems with L*, then certify closure by kernel decide. Our traps already follow the pattern "learn, then verify closure".
  - (b) Encode word families with a base-2 parameter, so one check covers every parameter.
  - (c) Test each proposed first-order structural lemma on rules 90, 150 and 210, whose space–times are 2-D automatic, before trying it on rule 30.
- **Obstacle.**
  - Walnut decides only first-order statements about automatic structures, and c needs ≥ 8,191 states.
  - The hard part of Absorption is entry into the trap, not its closure.
- **Artifacts.** Walnut (GPL-3.0); the commands printed in the diary.

#### C5. Dibujaron/rule30: a Lean library built by Claude agents
*Promise: medium for porting lemmas. Verification: Formal (3rd party), not rebuilt.*
- **Origin.** Drew McPolstra, [Dibujaron/rule30](https://github.com/Dibujaron/rule30), 2026-09-05 to 2026-09-13.
- **AI.** A "prove-one" dispatcher runs one Claude Code worker per node of a lemma DAG and checks each result with `lake build` and an axiom check.
- **Proved.** 167 single-theorem files (Lean 4.33.1 with Mathlib). Our scan found no `native_decide`, and `sorry` only in the statement files. Highlights:
  - Jen for any two columns.
  - A black run starting at time a ≥ 1 is shorter than a; a white run is shorter than 3a. Both sanity-checked on 60,000 bits.
  - Both colours occur in every interval [a, 4a]; there are ≥ n ones and ≥ n zeros among the first 5ⁿ bits.
  - Density → ½ iff an excess condition holds; `exists_config_same_centerColumn`.
- **Forms.** Problem 1 through two-column and white-times criteria; `return-words` (run bounds); Problem 2 (density iff excess).
- **Idea.** Many small, independently checked lemmas, scheduled along a dependency DAG.
- **Transfer.** Port the run bounds, the density–excess equivalence and the white-times criteria. The DAG harness design can be reused for the equivalents library.
- **Obstacle.** Nothing here excludes a nonconstant period. The run bounds are edge-region facts.
- **Artifacts.** No licence: ask before copying.

#### C6. Transducer fixpoints (Conway's cosmological theorem)
*Promise: low. Verification: peer-reviewed.*
- **Origin.** P. Lairez and A. Storozhenko, [arXiv 2409.20341](https://arxiv.org/abs/2409.20341) (2024-09-30); Amer. Math. Monthly 132(9) (2025) 867–882.
- **AI.** None (C++ automata computation).
- **Proved.** A computer-assisted proof of Conway's cosmological theorem, by composing and minimising transducers until a stabilisation identity holds.
- **Forms.** The shape of Q01 and Absorption: "every orbit eventually enters a set".
- **Idea.** Compose and minimise transducers until a regular language of decomposable states stops changing.
- **Transfer.** One rule-30 step on finite words is a transducer, so the same fixpoint search can be run on the driven halves.
- **Obstacle.**
  - There is no splitting lemma: rule 30 has positive entropy and two-way information flow.
  - Death and absorption times grow with the width, so no stabilisation step k is uniform.
  - For Q01, B1 and B6 bar stabilised regular certificates. For Absorption no such barrier is proved; the measured trap-avoiding paths keep the full growth rate.
- **Artifacts.** [ConwayTransducer](https://github.com/AleksandrStorozhenko/ConwayTransducer) (no licence).

#### C7. Diagonal defect front and Theorem H*
*Promise: low. Verification: preprint.*
- **Origin.** Berzai Part III ([rule30-left-edge](https://github.com/nateberzai-svg/rule30-left-edge), 2026-09-16 to October); [Dibujaron/rule30](https://github.com/Dibujaron/rule30) (commits of 2026-09-07/08).
- **AI.** Part III was contributed by three Claude Opus 5 referee dialogues; Dibujaron's lemmas by Claude agents.
- **Proved.** Each left diagonal splits into a periodic background and a finite defect. Conjecture H (τ_d ≥ d for d ≥ 20) is reduced to two front inequalities and certified on [20, 4×10⁶].
- **Forms.** Diagonals (solved; related statements in CATALOG.md) and Wolfram's 2019 auxiliary question, not Problem 1.
- **Idea.** Track the front of the defect along each diagonal.
- **Transfer.** Bookkeeping only.
- **Obstacle.** Rule 60 (τ_d = d + 1, constant centre) shows that Conjecture H decides neither Problem 1 nor Problem 2.
- **Artifacts.** Berzai (MPL-2.0); Dibujaron (no licence).

#### C8. Formal word libraries
*Promise: low. Verification: formal.*
- **Origin.** Isabelle [Combinatorics_Words](https://www.isa-afp.org/entries/Combinatorics_Words.html) (Holub, Raška, Starosta; 2021–2024); LAMP ([arXiv 2606.28841](https://arxiv.org/abs/2606.28841), 2026-06-27); Sequencelib ([arXiv 2601.11757](https://arxiv.org/abs/2601.11757), 2026-01-16).
- **AI.** LAMP is a multi-agent prover built on Kimi K2.6. The Isabelle library involves no AI. Sequencelib transpiles synthesised programs.
- **Proved.** Isabelle: Fine–Wilf, Lyndon–Schützenberger and more, for finite words only. LAMP closed 96.7% of 90 textbook theorems, but not Fine–Wilf. Sequencelib: over 25,000 OEIS definitions, without rule 30.
- **Forms.** `morse-hedlund`, `special-factors` (infrastructure).
- **Idea.** Reuse finite-word lemmas instead of re-proving them.
- **Transfer.** A source of finite-word lemmas when formalising C3. In Lean, Morse–Hedlund exists in our `ShiftOrbit.lean` and in Stephan's `InfiniteComplexity.lean` (B4).
- **Obstacle.** Finite words only; nothing about infinite sequences or automata.
- **Artifacts.** AFP licence; Sequencelib CC-BY-SA-4.0; the LAMP repository was not found.

#### C9. Normality and irreducibility forms (Problems 2 and 3)
*Promise: low. Verification: preprint and peer-reviewed.*
- **Origin.**
  - Fomin, Zenodo [22646809](https://zenodo.org/records/22646809) (v6 2026-09-07).
  - J. D. Howe, Zenodo [21798263](https://zenodo.org/records/21798263) (2026-08-04).
  - eliottcassidy2000 ([corpus](https://github.com/eliottcassidy2000/math), from 2026-08-24).
  - J. Natal and O. Al-saadi, [Complex Systems 34(3) (2025) 259–271](https://doi.org/10.25088/ComplexSystems.34.3.259) ([arXiv 2409.07065](https://arxiv.org/abs/2409.07065), 2024-09-11).
- **AI.** Howe: "substantial assistance" from Claude and GPT-5.5 Pro. eliottcassidy2000: Codex sessions. Natal–Al-saadi: none stated.
- **Proved.**
  - Fomin: density and halving statements reduce to a square-root discrepancy bound for one deterministic orbit.
  - Howe: for i.i.d. drivers, 4^(−k) decorrelation, plus twelve documented routes that do not transfer to the deterministic case.
  - Dibujaron: density iff excess (Lean). eliottcassidy2000: Cesàro balance iff o(2^m) dyadic discrepancy, and a counterexample to "history depth" as a query lower bound.
  - Natal–Al-saadi: row n of any 1-D cellular automaton in O(n²/log n). This is the only peer-reviewed Problem-3 upper bound found.
- **Forms.** Problems 2 and 3 (CATALOG.md); the stronger statement "normality".
- **Idea.** Reduce density statements to discrepancy, and irreducibility to explicit simulation costs.
- **Transfer.** Mauduit–Rivat-type exponential sums are the only technology that fits Fomin's reduction.
- **Obstacle.** Measure-level statements fail F-FIN; the single seed is invisible to them.
- **Artifacts.** Fomin (CC BY 4.0, code MIT); Howe (CC BY 4.0); eliottcassidy2000 (no licence).

#### C10. Maximum-order and expansion complexity *(added after the audit)*
*Promise: low. Library value: low (the register form is already proved). Verification: peer-reviewed (classical facts).*
- **Origin.** Survey by Chunlei Li (Bergen), [arXiv 2405.08479](https://arxiv.org/abs/2405.08479) (2024-05-14, v4 2026-04-13). Z. Chen, Z. Chen, J. Obrovsky and A. Winterhof relate maximum-order and 2-adic complexity ([arXiv 2309.12769](https://arxiv.org/abs/2309.12769), 2023-09-22). Expansion complexity: Mérai, Niederreiter and Winterhof (2017).
- **AI.** None.
- **Proved.**
  - A binary sequence is eventually periodic iff its N-th maximum-order complexity is bounded, because a bounded-order nonlinear feedback register is a finite-state map.
  - By Christol and Mérai–Niederreiter–Winterhof, it is 2-automatic iff its expansion complexity is bounded.
  - Relations between maximum-order, 2-adic and linear complexity.
  - Greenfeld–Moreira–Zelmanov ([arXiv 2408.03403](https://arxiv.org/abs/2408.03403)): every non-decreasing, submultiplicative function of at least linear growth is the complexity of some subshift.
- **Forms.** `nlfsr`, already proved in register form (`problem1_iff_no_feedback_shift_register` in [WordsAutomata.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/WordsAutomata.lean)); `cobham-christol` (expansion complexity; a stronger statement); `fcsr-complexity` and `series-f2-lfsr` through the relations between complexities.
- **Idea.** Maximum-order complexity is set by the longest factor that occurs twice with different successors. Bounding it is exactly "right-determinism at a fixed window", the same lemma behind Stephan's infinite Morse–Hedlund (`isEventuallyPeriodic_of_rightDeterministic`).
- **Transfer.** Two cheap entries: the complexity-profile wording of `nlfsr` (a short bridge from the register form), and "c is not 2-automatic iff its expansion complexity is unbounded" for the stronger statements.
- **Obstacle.** Equivalences only; they restate the difficulty. By Greenfeld–Moreira–Zelmanov, complexity growth alone cannot force more than Morse–Hedlund does. The data on c (all length-44 windows distinct in 10⁷ bits) say nothing asymptotic.
- **Artifacts.** The survey; Stephan's CC0 `InfiniteComplexity.lean` and `SubwordComplexity.lean` (axiom-free closures).

### D. Dynamics, constrained systems, certificates

#### D1. Period 1 for every nonzero finite configuration
*Promise: medium as infrastructure. Verification: preprint (Condrey); Formal (3rd party; foundry Lean, not rebuilt) for the period-1 chain.*
- **Origin.**
  - D. L. Condrey, [arXiv 2609.09431](https://arxiv.org/abs/2609.09431) (2026-09-08; CC BY 4.0).
  - rule30-foundry, branch [research/period2-column-ladder](https://github.com/Patto1155/rule30-foundry/tree/research/period2-column-ladder/formal) (commit c496996b, 2026-10-15): 50 declarations in core Lean v4.19.0 with standard axioms, including `finite_nonzero_not_eventually_constant`.
  - placego PROOFS.md entry 37 (hand proof, 2026-10-09).
- **AI.** Condrey: "anthropic/claude-opus-5 assisted with drafting, with the audit and figure scripts, and with locating references"; the author checked everything, and Jarkko Kari read an earlier version. The foundry formalisation was done by agents.
- **Proved.**
  - The same right half and centre trace force equal configurations.
  - The zero-trace fibre has prefix-OR form; the all-ones fibre has a checkerboard left half.
  - No column of a nonzero finite orbit is eventually constant. (Lean, foundry.)
  - The paper proves a sharp horizon of w + 2. The foundry README says "Sharp prefix horizons are not formalized", and the no-00000 constraint is not formalised either.
  - For period 2, the paper gives H(2, w) ≥ w **only as a sketch** (§5) and states "we make no claim about it or any higher period". The draft listed both horizons as proved and backed by Lean; that was wrong.
- **Forms.** `eventual-word` at period 1; FinConf at period 1 (stronger statements in CATALOG.md); `stripe-seeds` shows why seed-free results matter.
- **Idea.** Left-permutivity makes the configuration a function of the right half and the centre trace; a constant trace forces a rigid fibre.
- **Transfer.**
  - Our catalog's `no_column_eventually_constant` is a 10-line argument: local monotonicity plus `Rule30Jen.not_adjacent`.
  - Generalising `not_adjacent` to every nonzero finite configuration (Kopra: every number-like configuration) gives Condrey's corollary immediately.
  - placego's Proposition 20 shows infinitely many finite seeds share the single cell's centre column, so seed-free theorems are strictly more useful.
- **Obstacle.** The period-1 mechanism does not extend: a constant wall lets column 1 turn black only once.
- **Artifacts.** Condrey's ancillary files (CC BY 4.0); foundry `formal/Rule30/Basic.lean` and `ColumnReduction.lean` (no licence).

#### D2. The exact period-2 right-half language (rule30-foundry), extended, then demoted
*Promise: low as a route (demoted after the audit); medium as input data. Verification: preprint (foundry DRAT); counts and minimal forbidden words reproduced by two independent enumerators up to L = 15, and by the audit to L = 16.*
- **Origin.** [Patto1155/rule30-foundry](https://github.com/Patto1155/rule30-foundry/tree/research/period2-column-ladder), commit c496996b (2026-10-14/15): [period2_column_ladder.md](https://github.com/Patto1155/rule30-foundry/blob/research/period2-column-ladder/docs/theory/period2_column_ladder.md) and period2_column_reduction.md.
- **AI.** A Codex council and Claude agent branches, with a separate formalisation agent.
- **Proved** (with centre c(t) = t mod 2 and u_s = x₁(2s)):
  - Odd-left latch: x_{−1}(2s+1) = 1.
  - NOR return, which implies u has no factor 11.
  - Exact language counts 2, 3, 5, 8, 12, 17, 25, 36, 50, 68, 91, 119 for L = 1..12, with 12 MFWs: 11, 00000, 101001, 0100101, 010010001, 0101010000, 0101000101, 01010001001, 10010001001, 010010000101, 010100010001, 100100010000. These are DRAT-certified.
  - W_N(r) → ∞ iff period 2 is excluded for finite rows.
  - **L4 conjecture:** 7·weight(completion(u, N)) ≥ N − 8 for every u avoiding the 12 MFWs. It would exclude period 2. The weaker L1–L3 were refuted by u = (01)^45 000101, and the L4 queries at N = 191 and 300 returned UNKNOWN.
- **Computed** (draft, confirmed by the audit):
  - L = 13–15 give counts 156, 199 and 251 and seven new MFWs: 0001000010001, 1001000010001, 10101000010000, 01000010001001, 00100010000101, 010000100010000, 001000100001001.
  - L = 16 gives count 316 and two new MFWs, 1000100001010001 and 0101000010000101. The audit's enumerator runs L = 15 in 7.9 s and L = 16 in 32 s on the laptop; the draft's projection of about 80 s, and its plan to send L ≥ 16 to SAT or a pod, were wrong.
  - All nine kernel-checked eventual laws of `Rule30PeriodTwoWidth6`, and hence those of Width5, follow from MFWs of length ≤ 13 at every position ≥ 1.
  - Filtering the Q01 search by the 19 MFWs cuts the maximal survival at W = 56 from 100 to 67. Filtered survival is 116 at W = 96, 151 at W = 128 and 171 at W = 144. Adding the two L = 16 MFWs changes none of the maxima the audit re-ran (W = 56, 96 and 128); only the multiplicity at W = 96 falls from 16 to 14.
- **Why it was demoted.** Exact realizability (D12) kills the extremal filtered survivors far earlier: the best at W = 96 (filtered death 116) dies at about 57, through an MFW of length 18; the best at W = 128 (151) at about 99, through an MFW of length 37. All 103 leaves at W = 96 with filtered deaths 110–116 die by 87. Consequences:
  - The language has MFWs of length ≥ 37 and is very unlikely to be a shift of finite type.
  - A plateau of excess/W "as L grows" is an artefact of short L. The draft's kill rule, which stopped the route on such a plateau, was wrong.
  - The finite-size growth of about ×1.26 per symbol (about 0.33 bits) is about 2.7 times placego's channel ceiling of 0.122 bits per visible bit, and over four times the measured 0.07–0.08, so most of the constraint is long-range.
  - Porting MFWs by bit-sliced kernel checks over 2^(2L−1) windows is infeasible at L = 18 or 37.
- **Forms.** `eventual-word` for the word 01, through CQ01 (a project period reduction in CATALOG.md, and the period-2 case of `coupled-halves` with finite halves).
- **Idea.** Because u = ¬f (`p1_odd`), every right-half law constrains the left problem. Light-cone laws are exact finite computations, and they hold at all times for every right half.
- **Transfer.** Q01_lang ("every finite ZBL start whose u avoids the light-cone MFWs eventually dies") is a valid intermediate statement: Q01 ⇒ Q01_lang ⇒ CQ01 ⇒ no eventual period 2. It escapes the Q01-only witnesses, because truncated stripes violate 00000. Keep it as a Lean statement if it helps, but drive the search by D12.
- **Obstacle.**
  - Left truncations of the ether keep u in the language and survive about W steps (computed). A B1-style lasso for this setting is therefore likely, but it is not proved. B7's two-sided variant (derived) applies to additive rankings at centre flips.
  - L4 is a relaxation, so it may be false even if period 2 is excluded.
- **Artifacts.** Foundry (no licence). Ours: `ulang.c`, `dfs_lang.c`; the audit's `ulang_indep.c`, `dfs_lang21.c`, `subsume_indep.py` (scratch paths in Appendix A).

#### D12. Exact light-cone realizability by SAT in the loop *(added after the audit)*
*Promise: medium. It is the best concrete tool for period 2; it measures, it does not prove. Verification: preprint (placego; cake_lpr-checked cuts, not run by us); computed (the audit, with z3; spot-checked again here).*
- **Origin.** [ghywel/placego](https://github.com/ghywel/placego): [PERIOD-TWO.md](https://github.com/ghywel/placego/blob/main/PERIOD-TWO.md) rows Q6 and Q10, and [RULE30-PRIZE.md](https://github.com/ghywel/placego/blob/main/RULE30-PRIZE.md) §8.83–8.96, 2026-10-09 to 2026-10-14. Replicated and extended by the audit of this portfolio on 2026-10-15.
- **AI.** Claude (Local and Cloud) and GPT agents in placego. The audit's z3 scripts were written by Claude.
- **Proved and computed.**
  - placego, using kissat and cake_lpr-checked cuts: R_real, the record zero runs of the forced left half with a realizable column 1, is exact to depth 120 and certified to 97. R_real(147) = 18, against an unconstrained R(d) ≈ 0.826d. Sampled lower bounds grow slowly, e.g. R_real(1035) ≥ 38.
  - Audit: minimal forbidden words of length 18 (010000101000010001) and 37 (1000010000100001000010100001010000100). The extremal survivors of the 19- and 21-MFW filters die at about time 57 (W = 96) and 99 (W = 128). All 103 leaves at W = 96 with filtered death 110–116 die by time 87, so D_exact(96) lies in [87, 109]. At W = 56 the extremal u is realizable up to its kill, so D_exact(56) = 67.
  - Rechecked here: one W = 96 survivor takes about 1.1 s (|u| = 58, longest realizable prefix 28); the first 10 leaves take 12 s, with a maximum exact death of 85.
- **Forms.** `eventual-word` for the word 01, through CQ01. CQ01 is FinConf restricted to period 2 from time 0 (CATALOG.md, stronger statements) and the finite-halves case of `coupled-halves`. Also Q01_lang (D2).
- **Idea.** For a candidate finite left history, ask a SAT solver whether ¬f is produced by any right window of width 2m − 1 under an alternating centre. That is exactly the coupled problem at bounded left width. It sees every forbidden word of every length at once, whereas any finite MFW list sees only the short ones.
- **Transfer.**
  - Replace "add MFWs by length" with a DFS that checks exact realizability incrementally (an incremental SAT solver keyed on u-prefixes), computing D_exact(W) and the R_real records.
  - Harvest MFWs from UNSAT cores.
  - Put each MFW into Lean as a small LRAT refutation of the cone CNF (about 2L² variables), replayed by the kernel only: a checker proved sound in Lean and evaluated with `decide`, not `native_decide` or `ofReduceBool`.
  - The lifetimes found are what a proof of CQ01 has to beat.
- **Obstacle.**
  - It is still a finite computation; placego left the all-depth record bound open.
  - The visible language keeps positive entropy (≤ 0.122 bits per symbol by the channel bound, about 0.07–0.08 measured), so the wall described in §1.1 remains.
  - Ether truncations stay in the language for about W steps, so the excess over W cannot fall much below 0. A B1-style lasso through the ether is likely; it is unproved.
  - A kernel-only LRAT path has to be built: PBLean runs its checker natively, and lrat-catcher must be treated as if it does (D10).
- **Artifacts.** placego scripts and cake_lpr certificates (no licence; ask first). The audit's `realize.py`, `minforb.py`, `exact_deaths.py`, `check_realize.py`, `ulang_indep.c`, `dfs_dump.c` and `dfs_lang21.c`, with `leaves96.txt` (ours; scratch paths in Appendix A).

#### D3. The forced left half: one object studied by three groups
*Promise: medium as a map of the problem; low as a route. Verification: Lean (ours); preprint (placego, foundry).*
- **Origin.** Ours: round 2 of the archive ([Rule30ZeroBoundary.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean), 2026-10-15). placego: [PERIOD-TWO.md](https://github.com/ghywel/placego/blob/main/PERIOD-TWO.md) and [RECORD-MAP.md](https://github.com/ghywel/placego/blob/main/RECORD-MAP.md), 2026-10-05 to 2026-10-14. Foundry: D2. Duplicates: Kim (Zenodo [22858358](https://zenodo.org/records/22858358), 2026-09-20), Woffinden (Zenodo [22065659](https://zenodo.org/records/22065659), 2026-08-23), eliottcassidy2000 [THM-4048](https://github.com/eliottcassidy2000/math/blob/main/01-canon/theorems/THM-4048-rule30-periodicity-balance-and-model-firewalls.md) (2026-08-24).
- **AI.** Claude Code agents (ours); Claude, GPT and an "Intel" swarm (placego); Codex and Claude (foundry); Claude and ChatGPT as tools (Woffinden); Codex (eliottcassidy2000); not stated (Kim).
- **Proved.**
  - Ours (Lean): Θ; `two_step_shift` (conjugacy to the full shift on the free bits); Q01 iff Θ is never finitely supported iff BWR; `count_constrained` (2^⌊W/2⌋); `q01_width_le_52` in the catalog, with W ≤ 56 in the archive. Computed: D(W) ≤ 2W + 8 for W ≤ 71, with four codes.
  - placego: LR iff R(d) is finite for every d. R(d) is exact for d ≤ 61, and R(d) ≤ d + 4 at every computed depth (about 0.826d). R_real (D12). No period-2 counterexample has its left edge within 248 cells of the centre.
  - Foundry: completion(u, N), W_N and L1–L4 (D2).
  - Kim, Woffinden and eliottcassidy2000 give the same reduction and add nothing new.
- **Forms.** `eventual-word` for the word 01, through Q01 and CQ01.
- **Idea.** Under period 2 the whole left half is a function of one column sequence; all questions become questions about that function.
- **Transfer.** The map in 1.3; D12 is the sharpest tool on it.
- **Obstacle.**
  - Θ has no finite description beyond depth about 15: Myhill–Nerode classes grow like 1.79^s, the ANF degree is about k/2, and the statistics look i.i.d.
  - A random-constraint model predicts D(W) ≈ 1.82W and matches the measured survival to 0.2%.
- **Artifacts.** Ours: [Rule30ZeroBoundary.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean), [research/progA-backdet/](research/progA-backdet/). placego, foundry and eliottcassidy2000: no licence. Kim CC BY 4.0; Woffinden CC BY-NC 4.0.

#### D4. Channel bound and counting form (placego)
*Promise: low. Verification: preprint; scripts not run by us.*
- **Origin.** placego §8.20, §8.33 and §8.51; [PERIOD-TWO.md](https://github.com/ghywel/placego/blob/main/PERIOD-TWO.md) §2 and §5, 2026-10-05/06.
- **AI.** Claude (Local and Cloud), with predictions committed before runs; GPT read the results.
- **Proved.**
  - Column-1 words beside 0101 produced by a width-m layer with a free input form a regular language, with entropy h ≤ log₂ λ_m. At m = 28 this is about 0.122 bits per visible bit; PERIOD-TWO.md quotes 0.1236 certified, and 0.1292 in integer arithmetic.
  - Counting lemma N_{w,j}(T) = N_{w,j}(1)/2^(T−1) for T ≤ j. This matches our `count_constrained`.
  - Measured: N_w(T) ≈ 2^(w − 1.05T + c).
- **Forms.** `eventual-word` for the word 01 (counting form).
- **Idea.** Compare the information column 1 can deliver with the information the wall needs.
- **Transfer.** This is the delivery side of a counting proof. Showing that keeping the wall costs more than about 0.124 bits per visible bit would exclude period 2.
- **Obstacle.**
  - The cost side is the open statement.
  - The measured law also holds for random centre words, and the true centre word has count ≥ 1 for every T. So a counting proof must use what is special about periodic words.
- **Artifacts.** placego (no licence).

#### D5. Rule 210 clearing front; LR is false for rule 210
*Promise: low; its value is the lesson. Verification: preprint.*
- **Origin.** placego [PROOFS.md](https://github.com/ghywel/placego/blob/main/PROOFS.md) entry 32, 2026-10-06 to 2026-10-08.
- **AI.** Proof by GPT (GC478), checked by hand by Claude (L285).
- **Proved.**
  - No finite rule-210 seed keeps a 0101 clock in the centre.
  - The left-only statement LR is nevertheless false for rule 210: a column 1 whose runs have lengths 1, 1, 2, 4, 8, … keeps the left half empty.
  - Rule 90 also has no period-2 centre (Proposition 5), so rule 30 is the only open sibling at period 2.
- **Forms.** `eventual-word` for the word 01, for a sibling rule; a template for CQ01.
- **Idea.** A clearing front sweeps the left half once the centre clock is fixed.
- **Transfer.** Left-only Q01 can be strictly stronger than Problem 1 needs, so prefer the coupled form (D12, F2). The transfer of the front argument to rule 30 is recorded as invalid: the marker M = P ∨ Q carries no information.
- **Obstacle.** The rule-210 mechanism does not exist in rule 30.
- **Artifacts.** placego (no licence).

#### D6. Integer side against a free constrained side: Mahler 3/2 and confinement certificates
*Promise: low. Verification: preprint (placego); Formal (3rd party, CC0) for the confinement certificates.*
- **Origin.**
  - placego [MAHLER.md](https://github.com/ghywel/placego/blob/main/MAHLER.md), 2026-10-14/15.
  - Stephan with Claude Code, [rwst/Confinement-Certificates](https://github.com/rwst/Confinement-Certificates), 2026-08-08 to 2026-09-12 (Lean v4.34.0-rc2).
- **AI.** Claude (Local and Cloud) leads placego's mathematics, with GPT reviews. Stephan's Lean is "in collaboration with Claude Code".
- **Proved.**
  - placego: K ∩ eK = {0} for e = 2, 3 and 13; "multiplier exclusions are filters, not levers".
  - Stephan: kernel-checked block certificates, for example Z_{3/2}(1/6, 13/24) = ∅. The largest check takes about 100 s and 12 GB. The README says everything uses the standard axioms and no native code.
- **Forms.** The constrained-system shape of Q01 and Absorption; Kopra's class (rule 30 and ×p/q automata are both rapidly left expansive).
- **Idea.** A lasso in a finite abstraction is harmless if an independent aperiodicity lemma kills every run that stays in it.
- **Transfer.** For rule 30 this needs every constrained infinite run to force an eventually periodic column. That is possible only when the abstraction's recurrent components are single cycles, i.e. when it has zero entropy.
- **Obstacle.** For Q01, B1 and B6 prove that every finite abstraction has a lasso. For CQ01 and Absorption no such barrier is proved, but every constrained language measured there has positive growth: the period-2 visible language carries about 0.07–0.08 bits per symbol (D4), trap-avoiding strip paths keep the full growth rate (F3), and the free-bit languages of the period-4 skeletons grow by 1.27–1.32 per period (F13). So a zero-entropy abstraction is not expected.
- **Artifacts.** placego (no licence); Confinement-Certificates (CC0).

#### D7. Busy-beaver certificate classes
*Promise: low after B7. Verification: Formal (3rd party) and peer-reviewed for their own targets.*
- **Origin.**
  - Regular closed tape languages (n-gram CPS, RepWL, FAR): [Coq-BB5](https://github.com/ccz181078/Coq-BB5) (BB(5) = 47,176,870, proved 2024-07-02; [arXiv 2509.12337](https://arxiv.org/abs/2509.12337)).
  - Weighted closed sets (WFAR): [Iijil1/MITMWFAR](https://github.com/Iijil1/MITMWFAR); a Lean port, `WFAR.lean`, is in [mfornet/busybeaver](https://github.com/mfornet/busybeaver) (2026-07).
  - Recurrence certificates: n-gram closure plus whole-tape pattern-count rankings in [carrino/Coq-BBB4](https://github.com/carrino/Coq-BBB4) (BBB(4) = 32,779,478; 2026-07/08).
  - String-rewriting termination by matrix interpretations: Yolcu–Aaronson–Heule ([arXiv 2105.14697](https://arxiv.org/abs/2105.14697), J. Autom. Reasoning 2023); Stephan's Antihydra rewriting system (rwst/bbchallenge, 2026).
- **AI.** None in the BB(5) methods. The WFAR Lean port was written with Claude Opus 4.8 and Aristotle. Coq-BBB4 was built with Claude (Claude Opus 5.5 commit trailers in October 2026) and Codex branches. Stephan's SRS note credits Claude Code.
- **Proved.** BB(5), BBB(4), and nontrivial weakenings of Collatz by SAT-found matrix interpretations (Collatz itself is not proved).
- **Forms.** Q01, CQ01 and Absorption as termination and reachability statements over all finite starts.
- **Idea.** Certify that an infinite process never halts with a finite object: a closed regular set, a weighted automaton, or a ranking.
- **Transfer.** Regular safety certificates cannot express our statements, which are termination and reachability statements. What remains open: max-plus (arctic) rankings, lexicographic rankings that decrease only over k steps, and the learned global rankings of D13. Reusable from mfornet: the `closed_set` tactic, verified FAR, WFAR and NGramCPS checkers, and the chunked, kernel-only Skelet #1 path (the same pattern as our Q01 chunks).
- **Obstacle.**
  - For Q01, B1 and B6 bar finite-state rankings, and B7 (derived) bars additive ones: BBB-style counts, potentials fitted by LP over pattern counts and, heuristically, polynomial matrix interpretations.
  - For CQ01, only local rankings at centre flips (JointBarrier) and additive ones (B7 two-sided, derived) are barred. A finite-state barrier along c7 truncations is conjectured, not proved (D9).
  - For Absorption, no barrier is proved.
  - The reason additive counts work for Turing machines and not here: a Turing machine changes one cell per step, so a count changes locally; a cellular automaton changes every cell, so an additive potential changes by a sum with mean zero over a random bulk.
- **Artifacts.** Coq-BB5 (MIT, `CoqBB5/LICENSE` only); MITMWFAR (MIT); mfornet/busybeaver (BSD-2-Clause, in `LICENSES/`); Coq-BBB4 (0BSD); rewriting-collatz (no licence); Stephan's SRS (CC0).

#### D8. Barrier B7: additive rankings cannot certify Q01
*Promise: none; it is a filter. Verification: derived here (2026-10-15), not machine-checked. It uses C6 (computed) and B2 (Lean).*
- **Origin.** Derived in this portfolio on 2026-10-15, after the naive ranking LP of Appendix B.6; script `additive_ranking_lp.py` (scratch path in Appendix A). The draft that first stated it is kept in [research/technique-survey.json](research/equivalents-survey/technique-survey.json).
- **AI.** Claude Code.
- **Statement.** Consider rankings of the form V(x) = Σ_d h(x_d, …, x_{d+r−1}) + B(wall window) + E(edge window) + a·width, with h of range r ≤ 8. No such V can be ≥ 0 and decrease by ≥ 1 on every surviving double step of the zero-driven left half. The same holds with piecewise-constant weights on finitely many regions anchored at the wall or the edge.
- **Proof sketch.**
  1. Whether a double step survives depends only on x₁…x₃. So any bulk word can sit between a surviving wall part and an edge part.
  2. The change of the bulk term is a sum of g over windows, where g is a local function on windows of length r + 4.
  3. A de Bruijn cycle of positive g-weight, pumped in the bulk, would make ΔV arbitrarily large. So no cycle is positive, and Bellman–Ford gives potentials ψ with g(e) ≤ ψ(head) − ψ(tail) on every edge.
  4. Rule 30² is surjective, so by Hedlund's theorem it maps the uniform measure on (r+4)-words to the uniform measure on r-words. The uniform circulation, which has full support, therefore has g-mean 0. Summing the slack ψ(head) − ψ(tail) − g ≥ 0 against it gives 0, so g = ψ(head) − ψ(tail) exactly.
  5. Then Σ h is conserved by rule 30² on finite configurations. By C6 every such law of range ≤ 8 is trivial, so V is a function of width, wall window and edge window. B2 (`no_local_ranking`) excludes that.
- **Forms.** Q01; with the two-sided variant, the centre-flip setting of CQ01.
- **Two-sided version.** The same argument, with C6 for rule 30 (range ≤ 10) and `no_joint_local_ranking`, bars additive rankings that decrease at every flip of the centre, which is the CQ01 setting. It has not been checked for Absorption.
- **Not covered:**
  - max-plus rankings such as front positions (B6 already bars one max-type family for Q01);
  - lexicographic or k-step rankings, which would need C6 for rule 30^(2k);
  - arbitrary position weights;
  - rankings valid only on special subclasses, such as stripe-prefix families, where front arguments did work;
  - global, non-additive rankings (D13).
- **Explains** the archive's 15 failed monovariants.
- **Pitfall.** An LP restricted to rows of width ≤ W is always feasible, because V = C − width works at bounded width (Appendix B.6). A numeric test must encode the all-width conditions through de Bruijn potentials.
- **Artifacts.** The script above; C6's `conslaw*.py` in [research/A-invsearch/](research/A-invsearch/).

#### D13. Learned ranking functions with formal checking *(added after the audit)*
*Promise: low. Verification: peer-reviewed.*
- **Origin.** M. Giacobbe, D. Kroening and J. Parsert, neural termination analysis ([arXiv 2102.03824](https://arxiv.org/abs/2102.03824), 2021-02-07; ESEC/FSE 2022). M. Giacobbe, D. Kroening, A. Pal and M. Tautschnig, neural model checking ([arXiv 2410.23790](https://arxiv.org/abs/2410.23790), 2024-10-31; NeurIPS 2024).
- **AI.** Neural networks are trained as ranking functions or proof certificates, then checked by SMT or SAT.
- **Proved.** Termination and temporal-logic properties of software and hardware benchmarks, with machine-checked neural certificates.
- **Forms.** Q01, CQ01 and Absorption in their termination and reachability forms.
- **Idea.** Fit a ranking function (a network over the whole state) to sampled traces, then discharge "decreases on every transition" with an exact solver. Counterexamples feed back into training (CEGIS).
- **Transfer.** D7 and D8 leave open exactly the non-additive, global, max-plus and lexicographic certificate classes: B7 bars only additive rankings of range ≤ 8, and B2 and JointBarrier bar only width plus bounded windows. Learned global rankings on ZBL or coupled rows are the natural AI search over that open space.
- **Obstacle.** Solver checks cover only bounded widths, where the pitfall of D8 applies (V = C − width works trivially). An all-width, parametric proof is still needed. For Q01, any ranking through a finite abstraction is barred by B1 and B6.
- **Artifacts.** The authors' code; licences not checked.

#### D9. Irregularity proofs by shadowing
*Promise: low; useful only as a screen. Verification: informal (bbchallenge); conditional, with Lean files cited but not public (Antihydra).*
- **Origin.**
  - The Skelet #17 (dyuan01, 2024-08-02) and Finned #3 (2023) irregularity proofs ([wiki](https://wiki.bbchallenge.org/wiki/Skelet_17)).
  - Stephan's Antihydra pumping obstruction ([antihydra_FAR.tex](https://github.com/rwst/bbchallenge/blob/main/Antihydra/antihydra_FAR.tex), 2026), conditional on an unproved statement about unbounded dips.
- **AI.** Claude Code (Stephan); none for the others.
- **Proved.** Informal proofs that Skelet #17 and Finned #3 admit no regular closed tape language. For Antihydra, a conditional theorem; its Lean file is cited but not public.
- **Forms.** Barrier theorems for all forms.
- **Idea.** A certificate class fails once it is continuous on the Cantor or 2-adic topology and some non-finite configuration satisfies the constraint forever: −1 in ℤ₂, the stripe, c7. This is the same mechanism as our B1 and B6.
- **Transfer.** **For CQ01, a finite-abstraction barrier along c7 truncations is a conjecture.** The pigeonhole argument behind B1 suggests it, but it has not been proved or stated in Lean. Stating and proving it is part of S7.
- **Obstacle.** The argument needs a concrete non-finite witness for each setting. For Absorption no barrier of this kind is known.
- **Artifacts.** Wiki text (CC BY); Stephan's note (CC0).

#### D10. SAT/LRAT certificates and bounded searches
*Promise: medium as engineering; none for Problem 1. Verification: peer-reviewed or preprint for the pipelines; computed for the searches.*
- **Origin.**
  - Verified pipelines: the empty-hexagon number h(6) = 30 ([arXiv 2403.17370](https://arxiv.org/abs/2403.17370), ITP 2024); lrat-catcher ([arXiv 2607.00815](https://arxiv.org/abs/2607.00815)); PBLean ([arXiv 2602.08692](https://arxiv.org/abs/2602.08692)); K₈(4,2) = 23 ([arXiv 2606.16688](https://arxiv.org/abs/2606.16688)).
  - Bounded searches, March–October 2026: [rule30-foundry](https://github.com/Patto1155/rule30-foundry); [Cliff-Lee/R30](https://github.com/Cliff-Lee/R30); [kwaneleb21](https://github.com/kwaneleb21-ctrl/rule30_band_sat_sweep_repo_resumable_debugged_rc10_20_direct); [vibemathing PR #2](https://github.com/vibemathing/problem-rule30-1/pull/2); placego; [avikj Cubical Agda](https://github.com/avikj/math/tree/main/research/rule30) (2026-09-11).
- **AI.** None reported for the pipelines. Codex and Claude (foundry); "machine-assisted" (Cliff-Lee); a "Web GPT" channel (vibemathing); an agent-driven checking service (avikj).
- **Proved.**
  - The empty-hexagon formalisation found "a small error" in the symmetry-breaking proof and a typo in the lex-order condition; the encoding itself was essentially unchanged. (The draft said it caught a flaw in the reduction; that overstated it.)
  - K₈(4,2) = 23: its kernel-only replay reportedly used 143 GiB (unconfirmed).
  - Finite facts only: no period ≤ 5×10⁶ in the first 10⁷ bits (foundry); DRAT-certified unsatisfiable instances (Cliff-Lee, kwaneleb21); periods 2–6 excluded for right halves ≤ 18 cells (placego); no rational with denominator ≤ 256 (avikj, claimed).
  - Ours (Lean): T + P ≥ 16359; no P ≤ 4096 with T ≤ 8192; Q01 for W ≤ 52.
- **Forms.** `finite-certificates`, `morse-hedlund` and `binary-irrational` on finite windows; finite instances of Q01 and CQ01.
- **Idea.** Let a SAT solver do the case analysis, and import its proof certificate.
- **Transfer.** Only kernel-only replay fits our trust standard. **PBLean executes its checker "as compiled native code", and lrat-catcher imports (up to 174 TB) through "Lean core's verified LRAT checker", the checker that `bv_decide` runs natively; treat both at the `bv_decide`/`ofReduceBool` trust level we rejected, unless a kernel-only path is shown.** Targets:
  - the long MFWs of D12, as small LRAT refutations;
  - Q01 beyond width 56;
  - t001 traps of width 23–46;
  - period-3 walls wider than 28.
- **Obstacle.** A finite window cannot certify an eventual statement. Condrey's sketched bound H(2, w) ≥ w (D1) and our edge-region barrier say why.
- **Artifacts.** EmptyHexagonLean (licence not checked); Cliff-Lee/R30 (MIT); the others mostly without a licence.

#### D11. Other busy-beaver-era and dynamics techniques

| Technique, origin, date and URL | Forms | Why it does not transfer |
|---|---|---|
| Arithmetisation of sporadic machines: BB(5) counters and Gray codes (busycoq and Coq-BB5, 2023–2024); LLM-written Rocq proofs for BB(6): mxdys reported 20 on 2026-08-15, of which 2 were confirmed ([BB6 branch](https://github.com/ccz181078/busycoq/tree/BB6)) | per-word exclusions | Needs exact macro rules. c(t) moves to a new diagonal every step. |
| Eventual-behaviour detection: translated cyclers, inductive rules, longitudinal acceleration ([wiki](https://wiki.bbchallenge.org/wiki/Translated_cycler), 2022–2026) | Absorption (reachability sublemmas) | These prove that orbits become periodic. Skelet #1 starts cycling only after about 5.4×10⁵¹ steps, so finite absorption statistics are weak evidence either way. |
| Backward reasoning, halting segment ([wiki](https://wiki.bbchallenge.org/wiki/Backward_Reasoning), 2022–2023) | Q01 and CQ01 by preimages | Backward trees never die: `barrier_exists`/`barrier_unique` and `column_realizable_unique`. |
| Cryptids: Antihydra, Hydra, Space Needle ([wiki](https://wiki.bbchallenge.org/wiki/Cryptids); the BB(6) page listed 698 holdouts up to equivalence on 2026-10-15) | the constrained-system shape | Same shape as our open statements, and no technique exists. "Probvious" heuristics have been wrong before. |
| Langton's ant: Gajardo–Lutfalla–Rao, "Ants on the highway" ([arXiv 2409.10124](https://arxiv.org/abs/2409.10124), 2024), on generalised ants with many or infinitely many highways; Etse, escape-time bounds (MFCS 2026; [arXiv 2606.26677](https://arxiv.org/abs/2606.26677)). The classical non-repetition argument for a confined ant (Bunimovich–Troubetzkoy, 1992) uses reversibility and a bounded domain. The draft attributed that argument to arXiv 2409.10124, which was wrong. | Q01-type "every finite start eventually does X" | Rule 30 is irreversible, and the ZBL edge escapes. |
| Diddy (Salo–Törmä, "Diddy: a Python toolbox for infinite discrete dynamical systems", [arXiv 2305.01375](https://arxiv.org/abs/2305.01375), 2023-05-02), which defines and analyses multidimensional SFTs and cellular automata; Life SAT results (Salo–Törmä, ICALP 2022 and TCS 2025; omniperiodicity, [arXiv 2312.02799](https://arxiv.org/abs/2312.02799)). The draft misnamed Diddy and said it answers only finite existence questions. | shift-space versions of the coupled constraints | Diddy could analyse the period-2 coupled constraint as a two-dimensional SFT (not tried), but shift-space properties do not see one finite orbit (F-FIN). |
| Aperiodic tilings: the hat ([arXiv 2303.10798](https://arxiv.org/abs/2303.10798)); Greenfeld–Tao (Annals 200, 2024) | whole-space aperiodicity | Whole-space aperiodicity would be false here: c7 and the stripe are infinite configurations with periodic centres. |
| Collatz cycle exclusion (Hercher, [arXiv 2201.00406](https://arxiv.org/abs/2201.00406)) | per-period exclusions | Needs an arithmetic constraint on the period, and none is known for rule 30. |

#### D14. Spin models whose ground states are rule-30 trajectories *(added after the audit)*
*Promise: low. Verification: preprint.*
- **Origin.** K. Sfairopoulos, L. Causer, J. F. Mair, S. Powell and J. P. Garrahan (Nottingham), [arXiv 2503.19572](https://arxiv.org/abs/2503.19572) (2025-03-25, v4 2026-04-06).
- **AI.** None stated.
- **Proved.** Classical spin models for rules 30, 54 and 201 whose ground states are exactly the cellular-automaton trajectories. The models are frustrated and can be described by local defect variables. A transverse field gives an order-by-disorder mechanism and quantum phase diagrams.
- **Forms.** None directly; a vocabulary for the ether, wall and defect picture behind Absorption and CQ01.
- **Idea.** Encode the local rule as zero-energy constraints of a local Hamiltonian. Space–time diagrams become ground states, deviations from a periodic background become local defects, and the nonlinearity shows up as frustration.
- **Transfer.** Phrase the coupled period-2 problem as a boundary-condition problem for the model (an alternating column 0, finite support at t = 0), with the ether as a defect-free sector and nucleation as defect dynamics. That might give cleaner coordinates for counting defects in Absorption.
- **Obstacle.** The results concern ensembles and ground-state phases, not single orbits, so F-FIN applies and the finiteness of the seed is invisible. Rule 54, which has a periodic centre, sits in the same framework, so any argument must separate it from rule 30.
- **Artifacts.** Paper only.

#### D15. Systematic solvability tests: pattern decomposition and influence-solvability *(added after the audit)*
*Promise: low. Verification: preprint.*
- **Origin.** H. Fukś (Brock), solving the initial-value problem by pattern decomposition, [arXiv 2512.24337](https://arxiv.org/abs/2512.24337) (2025-12-30). F. Hübner and S. W. P. Kim, "Influence-solvability: a systematic theory of (1+1)D solvability", [arXiv 2606.12538](https://arxiv.org/abs/2606.12538) (2026-06-10, v2 2026-10-12).
- **AI.** None stated.
- **Proved.** Fukś gives explicit closed-form solutions of the initial-value problem for rules such as 156. Hübner–Kim give local necessary and sufficient conditions for a (1+1)D brickwork circuit to be influence-solvable.
- **Forms.** `eventual-word`, through an exact global description of the driven halves.
- **Idea.** Decide mechanically, by local conditions or pattern decomposition, whether a 1+1D rule admits a closed-form or "solvable" description.
- **Transfer.** §4.4 lists an exact global description in special coordinates (Q-tilde style, F10) as a remaining candidate mechanism. These tests could decide quickly whether the period-2-driven right half beside 0101, or the ZBL, admits such a description in some coordinates, and so close or open that line.
- **Obstacle.** The archive already found that Θ has no finite description beyond depth about 15, and that the driven systems have positive entropy. Solvable classes are typically linear, dual-unitary-like or zero-entropy, which is the F-OR side.
- **Artifacts.** Papers only.

### E. Frontier-AI workflow patterns

#### E1. Lean-compiler feedback loops
*Promise: medium as tooling. Verification: formal outputs (Lean); the Science publication is reported only by secondary sources.*
- **Origin.**
  - AlphaProof Nexus, Google DeepMind ([arXiv 2605.22763](https://arxiv.org/abs/2605.22763), v1 2026-05-21; [results](https://github.com/google-deepmind/alphaproof-nexus-results)).
  - Open equivalents: Epoch's [LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems) ([arXiv 2608.11941](https://arxiv.org/abs/2608.11941), 2026-08-12); [OpenGauss](https://github.com/math-inc/OpenGauss); Archon ([arXiv 2604.03789](https://arxiv.org/abs/2604.03789)); LeanMarathon ([arXiv 2606.05400](https://arxiv.org/abs/2606.05400)).
- **AI.** Gemini 3.1 Pro agents loop on Lean errors, optionally with AlphaProof and evolutionary search. Humans chose the problems and checked statement fidelity.
- **Proved.** 9 of 353 Erdős statements and 44 of 492 OEIS conjectures; a basic agent alone replicated all 9 Erdős solves. OEIS Open: 147 of 492 at $50 per attempt.
- **Forms.** Any Lean statement: the library's `problem1_iff_*` theorems, `fc-bridge`, and the stated forms of CATALOG.md.
- **Idea.** Let the compiler's error messages steer the next attempt.
- **Transfer.** Point these loops at:
  - library equivalences (A1, B3, C3, C10, and the stated forms in CATALOG.md);
  - seed-free generalisations of Jen and Condrey (D1);
  - the Lean steps of shortlist items S1–S7.

  Joint search over a numeric parameter and its proof suits trap widths and window sizes.
- **Obstacle.**
  - Successes are short elementary arguments.
  - Known failure modes: offloading the core into a sorry'd lemma that restates the target, hallucinated literature lemmas, and misformalisation.
  - The barriers bind agents too.
- **Artifacts.** alphaproof-nexus-results (Apache-2.0); LeanOpenProblems (MIT; GitHub reports NOASSERTION); OpenGauss (MIT); Archon and LeanMarathon (Apache-2.0).

#### E2. Evolutionary program search
*Promise: medium, for sub-hypotheses only. Verification: preprint.*
- **Origin.**
  - AlphaEvolve ([arXiv 2506.13131](https://arxiv.org/abs/2506.13131), 2025-05-14); Georgiev, Gómez-Serrano, Tao and Wagner ([arXiv 2511.02864](https://arxiv.org/abs/2511.02864), 2025-11-03).
  - Open implementations: [OpenEvolve](https://github.com/algorithmicsuperintelligence/openevolve) and [ShinkaEvolve](https://github.com/SakanaAI/ShinkaEvolve).
  - Knuth's "[Claude's Cycles](https://cs.stanford.edu/~knuth/papers/claude-cycles.pdf)" (2026-02-28).
- **AI.** Gemini models mutate programs scored by user-written evaluators. In Knuth's case Claude Opus 4.6 ran brute force and simulated annealing, found a general construction, and Knuth proved it.
- **Proved.** AlphaEvolve matched most known constructions and improved some. It failed on Erdős discrepancy (length 380 with a hint, against 1160 by SAT) and showed a "cheating phenomenon" against leaky evaluators.
- **Forms.** Sub-questions: Q01 survival, traps for Absorption, walls for the period-3 ether, C3w(011).
- **Idea.** Evolve programs against a numeric score.
- **Transfer.** Use it only where a graded score exists:
  - long-surviving ZBL starts beyond W = 71, and coupled starts scored by exact death (D12);
  - right halves driven by 011 that might refute C3w(011);
  - SAT-in-the-loop heuristics for traps of width 21–46 and period-3 walls wider than 28.
- **Obstacle.**
  - B7 (derived, D8) rules out "evolve an additive potential" for Q01.
  - Finite-horizon evaluators are leaky.
  - SAT beats LLM evolution on binary constraint search.
- **Artifacts.** OpenEvolve and ShinkaEvolve (Apache-2.0); AlphaEvolve problem repository (Apache-2.0).

#### E3. Counterexample-first and countermodel construction
*Promise: medium, as risk reduction. Verification: formal or computer-checked for the examples listed.*
- **Origin.**
  - Unit distances with n^(1+c) pairs, disproving [Erdős #90](https://www.erdosproblems.com/90) (OpenAI internal model, 2026-05-20). [arXiv 2605.20695](https://arxiv.org/abs/2605.20695) is a human-verified expository note by Alon, Bloom, Gowers, Litt, Sawin, Shankar, Tsimerman, Wang and others. The Lean proof is third-party ([plby/Erdos90](https://github.com/plby/Erdos90)), not OpenAI's.
  - A claimed counterexample to the Jacobian conjecture in dimension 3 (Claude Fable 5 with L. Alpöge, 2026-07-19). It was reproduced by computer algebra but is not peer-reviewed.
  - [Erdős #619](https://www.erdosproblems.com/619) (2026-06-09) and [#1202](https://www.erdosproblems.com/1202) (2026-04-01); OEIS Open disproofs.
  - Countermodels: Kovač–Tao ([arXiv 2406.17593](https://arxiv.org/abs/2406.17593)); GPT-5.4 Pro on a #251 variant (2026-04-15); #263(ii).
- **AI.** General reasoning models propose explicit objects; computer algebra, Lean or human digests check them.
- **Proved.** The counterexamples above, each with an exact certificate.
- **Forms.** The open sub-hypotheses behind the project's period reductions (listed under Transfer).
- **Idea.** Try to refute a hypothesis before investing in it.
- **Transfer.**
  - Try to refute these hypotheses first: D(W) ≤ 2W + 8, C3w(011), C3s001, AbsorptionT t001, "no period-3 wall", the block law, and L4.
  - Build countermodels that satisfy everything a proposed strategy uses. `seed_perturbation`, the truncated stripes and c7 already follow this pattern.
  - Accept only exact certificates.
- **Obstacle.** It kills routes but proves nothing. Problem 1 itself is heavily supported: T + P ≥ 16359 is kernel-checked.
- **Artifacts.** plby/Erdos90 (licence not checked); OEIS Open results (no licence file).

#### E4. Finite-invariant and closed-form certificates (what AI provers usually find)
*Promise: low. Verification: formal (Lean, SafeVerify).*
- **Origin.** AlphaProof Nexus OEIS run (2026-05) and Epoch's OEIS Open ([arXiv 2608.11941](https://arxiv.org/abs/2608.11941), 2026-08-12).
- **AI.** Autonomous: the AlphaProof Nexus agent, and three frontier models in OEIS Open on a $50 budget.
- **Proved.**
  - OEIS [A267581](https://oeis.org/A267581), the single-seed centre of rule 167, proved by AlphaProof Nexus ([Lean](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_267581_conjecture_0.lean)) and independently by Claude Opus 4.8, GPT-5.5 and Gemini 3.5 Flash. The proof uses a closed form for the whole space–time plus Lucas' theorem (confirmed by the audit).
  - A382590, A100478, and A300997 (a mass-halving CA, via a conservation law).
- **Forms.** Problem-1 analogues for structured sequences; `morse-hedlund` through closed forms.
- **Idea.** Find a closed form or a finite invariant, then prove it by induction.
- **Transfer.** None for c; useful as calibration of what agents can do.
- **Obstacle.**
  - Rule 167 is not affine as a local rule, but on its single-seed orbit it acts from time 1 on as rule 165 = ¬(l ⊕ r), which is affine (a complemented Pascal triangle mod 2; checked here for 300 steps). So the F-OR barrier applies.
  - Finite-invariant and coupling certificates are barred by B1, B6 and C6 in the Q01 setting.
  - A214560 (the number of 0s in binary n² tends to infinity) is a digit-growth conjecture, not a randomness one. Our survey's "every model failed it" is not in the OEIS Open text the audit could read, so it is unverified.
- **Artifacts.** APN Lean files (Apache-2.0); LeanOpenProblems gold proofs (MIT).

#### E5. Literature identification by deep-research models
*Promise: medium. Verification: preprint and secondary reports.*
- **Origin.** GPT-5 episode, October 2025 ([report](https://the-decoder.com/leading-openai-researcher-announced-a-gpt-5-math-breakthrough-that-never-happened/)); Aletheia ([arXiv 2601.22401](https://arxiv.org/abs/2601.22401)); Tao's [wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems) (data to 2026-06-30).
- **AI.** LLM literature search; humans confirm the sources.
- **Proved.** Nothing new.
  - GPT-5 found published solutions to about 10 Erdős problems listed as open; the announcement that it had "solved" them was deleted.
  - Tao's wiki lists 84 literature-search rows.
  - Aletheia: 9 of its 13 meaningful answers were found in or rediscovered from the literature (v3 full text; its abstract still says 8).
  - "Novel" AI solutions to #333, #397, #281 and #1026 turned out to be in the literature.
- **Forms.** All forms: salvage of known partial results.
- **Idea.** Ask a model where a sub-question has already been answered.
- **Transfer.** Run de-identified searches for each sub-question: traces of left-permutive CA, number-like configurations, odometer factors. This survey found, for example, the Gravner–Griffeath and Ikram precursors only through the audit.
- **Obstacle.** Citations can be hallucinated. First Proof grades citation adequacy as a category; the per-model figure in our survey (4 of 10 GPT-6 Astra answers in batch 3) is not in public text and is unverified.
- **Artifacts.** Aletheia raw outputs (google-deepmind/superhuman, Apache-2.0).

#### E6. Adversarial proof checking and kernel hygiene
*Promise: medium; a prerequisite for everything else. Verification: tools.*
- **Origin.**
  - [Comparator](https://github.com/leanprover/comparator) (repository created 2025-06-06), lean4export and lean4checker.
  - [nanoda](https://github.com/ammkrn/nanoda_lib), an independent kernel.
  - [SafeVerify](https://github.com/GasStationManager/SafeVerify) and [LeanParanoia](https://github.com/math-inc/LeanParanoia).
  - FrontierMath Erdős ([arXiv 2609.25050](https://arxiv.org/abs/2609.25050)) §3.3 lists the attack classes: environment tampering, compile-time code, changed statements, redefinitions, assuming the result, and kernel bypass via `debug.skipKernelTC`, `addDecl`, `native_decide` or `implemented_by`.
  - T. Hales, guest post on Tao's blog, [2026-10-09](https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/).
- **AI.** This infrastructure exists to check AI-generated proofs.
- **2026 kernel bugs.**
  - #14484, opened 2026-07-22 by phulin; the report says it was "largely generated with AI", model not named. Fixed in v4.32.1 (2026-07-22).
  - [#14576](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/), opened 2026-07-28 after Ramana Kumar's AI-assisted Collatz "disproof" of 2026-07-25, which also used a separate nanoda bug fixed a week earlier. Fixed in v4.32.2 (2026-07-28). It is reachable only through metaprogramming that sends crafted declarations straight to the kernel.
- **Third-party artifacts on pre-fix toolchains:** rule30-foundry (v4.19.0), Ceiling-Orbits and Transcendence-Criteria (v4.33.0-rc1), openai/ten-proofs (v4.32.0), mfornet/busybeaver (v4.32.1, before the #14576 fix). Plectis pins v4.30.0, as our library does.
- **Our position.**
  - The catalog and the library pin v4.30.0.
  - A survey grep found no `addDecl`, `elab`, `macro`, `syntax`, `run_cmd` or `#eval` in our sources.
  - Toolchains v4.32.2, v4.34.0 and v4.35.0 are installed locally.
- **Forms.** All library files.
- **Idea.** A proof counts only if it replays through a pristine kernel in a sandbox against a trusted statement file, with identical dependencies and the three standard axioms.
- **Transfer.**
  - Write Comparator challenge files for `Problem1` and each `problem1_iff_*`.
  - Replay everything under v4.35.0 (rather than 4.32.2) and under nanoda.
  - Add test lemmas pinning the prefix of c.
  - Extend the source scan to `run_cmd`, `addDecl` and `debug.skipKernelTC`.
- **Obstacle.** None; it costs only time.
- **Artifacts.** Comparator, lean4export, lean4checker, nanoda and SafeVerify (Apache-2.0); LeanParanoia (MIT).

#### E7. Autoformalisation at scale and AI porting of certificates
*Promise: medium, for formalisation throughput. Verification: formal (company claims for speed).*
- **Origin.**
  - Gauss and [OpenGauss](https://github.com/math-inc/OpenGauss) (Math Inc.; strong PNT in September 2025, sphere packing in early 2026; the speed figures are company claims).
  - Aristotle (Harmonic; [arXiv 2510.01346](https://arxiv.org/abs/2510.01346), 2025-10-01).
  - Archon ([arXiv 2604.03789](https://arxiv.org/abs/2604.03789), 2026-04-04); LeanMarathon ([arXiv 2606.05400](https://arxiv.org/abs/2606.05400), 2026-06-03).
  - AxiomProver (Fel's conjecture, [arXiv 2602.03716](https://arxiv.org/abs/2602.03716), 2026-02-05).
  - BB(5) in Lean: [mfornet/busybeaver](https://github.com/mfornet/busybeaver) (July 2026).
- **AI.** Agents write Lean from LaTeX or blueprints, filling sorries in parallel under CI. The BB(5) port used Claude Opus 4.8 and Aristotle.
- **Proved.**
  - BB(5) was ported to Lean in a few weeks. Its value theorems use `native_decide`, which our policy rejects; Skelet #1 has a kernel-only path.
  - Claude Opus 4.6 ground through 140 BBf(21) holdouts (result marked "tentative").
- **Forms.** `fatou`, `natural-boundary`, `cobham-christol`, `two-adic` and Problem 2 definitions (infrastructure).
- **Idea.** Formalise existing arguments quickly; the statement is the human's job.
- **Transfer.** Formalise the heavy theorems behind the library forms (Szegő/Pólya–Carlson, Christol, Cobham, Kopra, Condrey, the Coven–Pivato–Yassawi odometer), and port the BB verifiers.
- **Obstacle.** Definitions and statements are the hard part ("Sorries Are Not the Hard Part", [arXiv 2606.13925](https://arxiv.org/abs/2606.13925)). AxiomProver's A6697 "solution" covers only a reduced statement.
- **Artifacts.** OpenGauss (MIT); Archon and LeanMarathon (Apache-2.0); busybeaver (BSD-2-Clause).

#### E8. Author–critic councils, prompting patterns and generate-and-kill swarms
*Promise: low. Verification: preprint and press reports.*
- **Origin.**
  - ProofCouncil (ETH; [arXiv 2607.09474](https://arxiv.org/abs/2607.09474), 2026-07-10), which reports First Proof batch 2.
  - DeepSeekMath-V2 ([arXiv 2511.22570](https://arxiv.org/abs/2511.22570), 2025-11-27).
  - The Gemini case studies ([arXiv 2602.03837](https://arxiv.org/abs/2602.03837), 2026-02-03): de-identify famous problems, prompt "prove or refute", and scaffold the lemmas.
  - Rule 30 swarms: placego SW-01 (RULE30-PRIZE.md §8.113, 2026-10-14/15); Condrey's [BlindMind](https://github.com/dcondrey/blindmind/blob/main/headless_evolve_rule30.py) roundtables (2026-08-31 to 2026-10-13); Fomin's ten-lens assaults ([Zenodo 22646809](https://zenodo.org/records/22646809)); Berzai's closed-routes table; Howe's 12 routes ([Zenodo 21798263](https://zenodo.org/records/21798263)).
- **AI.** Multi-model author and critic agents. ProofCouncil runs GPT-6 Astra Pro, GPT-6 Astra, Claude Fable 5.1, Claude Sonnet 5 and Gemini 3.1 Pro. SW-01 ran on Fable 5.1 and Opus 5.5 agents; BlindMind uses the Claude CLI.
- **Results.**
  - First Proof: batch 2, ProofCouncil 6 of 10; batch 3 (2026-10-14), ProofCouncil 9 of 10 and a Kimi K3 harness 0 of 10 (Scientific American). ProofCouncil is not independent of GPT-6 Astra, and a separate "GPT-6 Astra 7 of 10" figure is unverified (1.4).
  - SW-01: 10 proposals; 0 survived, 2 wounded (#5 and #7, both about Erdős's ternary digits of 2ⁿ), 8 died. 134 flags were raised: 28 confirmed and 68 partly confirmed, 96 real. Only proposals #3, #9 and #10 concerned rule 30.
  - Condrey's roundtables: 13 or more directions, all reduced to three dead shapes: bounded-strip or cone-width propagation; ergodic or mutual-information statements that are trivial on one orbit; circuit or preimage counting with no real lower bound.
- **Forms.** None directly; review of natural-language steps for any form.
- **Idea.** Separate the author from the critic, and kill proposals with fixed filters.
- **Transfer.** Adopt their filters:
  - the rule-90/150/210 firewall;
  - the prefix check: every finite word extends to an automatic sequence;
  - the single-orbit versus measure check;
  - placego §8.116's four kinds of single-object proof that have ever worked: finite certificate, valuation or digit obstruction, exact identity with a uniform error bound, explicit construction.
- **Obstacle.** Councils filter; they do not supply the missing global idea.
- **Artifacts.** eth-sri/proof-council (MIT); DeepSeek-Math-V2 weights (Apache-2.0); blindmind (Apache-2.0); placego (no licence).

#### E9. RL-trained provers and large agent swarms
*Promise: low. Verification: benchmark results; for the swarms, formal claims partly audited.*
- **Origin.**
  - RL provers, April to December 2025: AlphaProof ([Nature, 2025-11-12](https://research.google/pubs/olympiad-level-formal-mathematical-reasoning-with-reinforcement-learning/)), DeepSeek-Prover-V2 ([arXiv 2504.21801](https://arxiv.org/abs/2504.21801)), Kimina-Prover ([arXiv 2504.11354](https://arxiv.org/abs/2504.11354)), Goedel-Prover-V2 ([arXiv 2508.03613](https://arxiv.org/abs/2508.03613)), Seed-Prover 1.5 ([arXiv 2512.17260](https://arxiv.org/abs/2512.17260), 2025-12-19).
  - Swarms: OpenAI's [ten proofs](https://github.com/openai/ten-proofs) (announced 2026-08-01).
- **AI.** RL on a Lean-verifier reward; unreleased OpenAI models for the swarms.
- **Proved.**
  - Seed-Prover 1.5: 88% of PutnamBench; its authors call most of its Erdős results simple or misformalised.
  - OpenAI's ten proofs come with Lean 4.32.0 certificates and Comparator configurations. They are not unreviewed, as the draft said: Sienicki & Sienicki ([arXiv 2608.14673](https://arxiv.org/abs/2608.14673), v3 2026-09-09) audit 18 chapter reviews and find no confirmed substantive error remaining in a principal result; Chapter 8 has a request for major revision; follow-up work confirms the disproof of Connes's rigidity conjecture. The toolchain v4.32.0 predates both 2026 kernel fixes.
  - OpenAI's other swarm claims: a finite-time singularity for Navier–Stokes with forcing (2026-09-08; 166 pages plus Lean), contested and not accepted by Clay ([report](https://thenextweb.com/news/openai-navier-stokes-claim-verification-credit)); and CDC (2026-07-10), a natural-language proof only, unverified ([Oum's exposition, arXiv 2607.16356](https://arxiv.org/abs/2607.16356)).
  - Calibration: FrontierMath Erdős gives 2 of 68 at $300 and 5 of 68 above $220k.
- **Forms.** Lean infrastructure; families of finite instances.
- **Idea.** Train on many variants of a target, or run thousands of agents.
- **Transfer.** Our sub-questions come in graded families (Q01 by width, Absorption by word), which suit test-time RL. Open-weight provers could fill routine library lemmas on a pod, with user approval.
- **Obstacle.** Scale has not produced a result on a statement of our kind.
- **Artifacts.** Goedel-Prover-V2 (Apache-2.0); Kimina-Prover (MIT); Seed-Prover (Apache-2.0); ten-proofs (Apache-2.0).

#### E10. PatternBoost: transformer-guided local search *(added after the audit)*
*Promise: low. Verification: preprint.*
- **Origin.** F. Charton, J. S. Ellenberg, A. Z. Wagner and G. Williamson, PatternBoost, [arXiv 2411.00566](https://arxiv.org/abs/2411.00566) (2024-11-01). Its predecessor FunSearch: Romera-Paredes et al., [Nature 625 (January 2024)](https://www.nature.com/articles/s41586-023-06924-6).
- **AI.** A transformer is trained on the best constructions found and alternates with classical local search. FunSearch uses LLM-guided program search.
- **Proved.** New and best-known constructions in several extremal-combinatorics problems. These are constructions and counterexamples, not proofs.
- **Forms.** Finite-time near-counterexamples for CQ01, Absorption, C3w(011) and L4 (S8).
- **Idea.** Train a generative model on the top-scoring candidates, sample new ones, polish them by local search, and repeat.
- **Transfer.** Search for finite left/right row pairs that maximise exact coupled survival (score = exact light-cone death, D12) beyond the widths where DFS and SAT are exhaustive (W > 150). This stress-tests D(W) ≤ 2W + 8 and any proposed CQ01 lifetime bound. E2 did not cover it.
- **Obstacle.** It cannot prove anything. At the widths that matter, SAT and exhaustive DFS already dominate. Leaky finite-horizon scores could reward artefacts.
- **Artifacts.** PatternBoost code released by its authors (licence not checked); FunSearch reference code (Apache-2.0, not checked here).

#### E11. Equational Theories Project: mass case closure, every case Lean-certified *(added after the audit)*
*Promise: low. Verification: Formal (3rd party; every case checked in Lean), not rebuilt.*
- **Origin.** T. Tao and about 50 collaborators (M. Bolan, J. Breitner, N. Carlini, M. Carneiro, F. van Doorn and others), [arXiv 2512.07087](https://arxiv.org/abs/2512.07087) (paper 2025-12-08; project 2024–2025); [teorth/equational_theories](https://github.com/teorth/equational_theories).
- **AI.** Automated theorem provers (Vampire, egg) and finite-model finders (Mace4) at scale, with some LLM assistance; every outcome checked in Lean.
- **Proved.** All of the roughly 22 million implications among 4694 magma laws, with Lean-verified proofs and counterexamples, including greedy infinite countermodels.
- **Forms.** `eventual-word`, as a census (S3); countermodels for sub-hypotheses (S8).
- **Idea.** Split a very large family of statements into machine-closable cases, attack them with several kinds of engine, and accept a case only when Lean certifies it, with a public dashboard of open cases.
- **Transfer.** A template for the word census of S3 (three engines; words of period 8–20 closed into Lean) and for systematic countermodels in S8. Its greedy infinite countermodels mirror how c7 and the stripe defeat local arguments.
- **Obstacle.** Every case there is a finite implication. Problem 1 is one statement about one orbit, so the infrastructure scales the census, not the core argument.
- **Artifacts.** equational_theories repository (licence not checked here).

### F. Our own salvage

All F cards come from our archive, [VibeProof/Rule30Prize](README.md) (2026-10-15; [write-up](https://sw1sh.github.io/vibe-proof/rule30-prize/)), produced by Nikolay Murzin with a Claude Code multi-agent workflow: attack agents, rigour, re-derivation and counterexample verifiers, and synthesis and integration agents (model IDs not recorded). Only kernel-checked results with the three standard axioms were accepted. The repository has no licence file. Lean modules are in [../lean/Ruliology/CellularAutomata/](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/lean/Ruliology/CellularAutomata).

#### F1. The masked Jen family
*Promise: medium; it is the interface every word exclusion must reach. Verification: Lean (ours).*
- **Origin.** 2026-10-15. Round 1: [Rule30MaskedJen.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean), [Rule30DrivenLeft.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30DrivenLeft.lean), [Rule30WhiteSeed.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30WhiteSeed.lean), on top of [Rule30Jen.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Jen.lean). Base theorem: [Jen 1986](https://link.springer.com/doi/10.1007/BF01010579).
- **AI.** Attack agents found and proved the masked and window forms. A verifier refuted one corollary in Lean (an off-by-one threshold in the doubling-window corollary), which was then repaired (`research/verify-c3-doubling/C3Rescue.lean`).
- **Proved.**
  - `masked_jen`, `orCol_not_eventuallyPeriodic`, `window_jen`, `finitary_jen`, `periodic_window`.
  - `Rule30DrivenLeft.no_periodic_column`: a finite nonzero left half driven by an eventually periodic boundary has no eventually periodic column.
  - `Rule30WhiteSeed.problem1_30_or_135`.
- **Forms.** `eventual-word`: every word exclusion ends with this lemma. The weaker statements "Jen's pairs and masked Jen" in CATALOG.md. `symmetric-rules`: [Symmetry.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/Symmetry.lean) treats rule 135 from a black seed as a different question.
- **Idea.** If column i has period P, column i+1 cannot also have period P on the white times of column i: left-permutivity carries a defect.
- **Transfer.** Any external technique must deliver column 1 eventually periodic at the white phases of w. Condrey's time-shift defect, Kim's identity L_{t+p} ⊕ L_t = (1 ⊕ C_t)(R_{t+p} ⊕ R_t) and the transferred Antihydra argument (A6) all land here.
- **Obstacle.** It needs a second periodic object, and under 0101 driving the output of the true right half has positive entropy.
- **Artifacts.** The Lean files above.

#### F2. Effective boundary and the reductions
*Promise: medium. Verification: Lean (ours) for every implication; all hypotheses are open.*
- **Origin.** 2026-10-15. Round 1 (small-periods agent; verifier verify-C1-effbdry-rigor), extended in round 2 and the final batch: [Rule30PeriodTwo.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwo.lean), [Rule30PeriodFourSkeleton.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean), [Rule30EtherThreeLeft.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherThreeLeft.lean), [Rule30PeriodTwoCoupled.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoCoupled.lean).
- **AI.** Found and proved by round-1 agents and adversarially verified; the derived reductions were written in round 2 and the final batch.
- **Proved.**
  - `effective_boundary`, `effective_step`.
  - Q01 ⇒ no eventual period 2 (`not_eventually_period_two_of_Q01`); Q01 ⇒ CQ01 ⇒ no eventual period 2 (`no_eventual_period_two_of_CQ01`).
  - C3(w) for 0001, 0011 and 0111 ⇒ no least period 4 (`least_period_four_of_C3`).
  - Q001 or C3s001 ⇒ no 001 tail; C3w(011) ⇒ no 011 tail.
- **Forms.** `eventual-word` for 01, 001, 011, 0001, 0011 and 0111; the stronger statement "effective boundary" and the project's period reductions in CATALOG.md; `coupled-halves`, whose left-half relaxations these are.
- **Idea.** The left half sees column 0 only through c(t) ∧ c(t+1). For a period word with no cyclically adjacent 1s, the left half after the onset is the autonomous ZBL started from a finite row.
- **Transfer.** This is where any "a finite orbit cannot satisfy a constraint forever" technique plugs in, word by word. D2 adds Q01_lang; D12 measures CQ01 directly.
- **Obstacle.** The constrained ZBL is conjugate to the full shift, and its survival statistics match an unbiased coin within 0.2%.
- **Artifacts.** The Lean files above; death-time searches in [research/progA-backdet/](research/progA-backdet/) and [research/A-invsearch/](research/A-invsearch/).

#### F3. Traps and Absorption (least period 4; the word 001)
*Promise: medium. The best partial target is Absorption(0111). Verification: Lean (ours) for the traps; computed for entry.*
- **Origin.** 2026-10-15. Rounds 1–2 and the final batch: [Rule30Ether.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Ether.lean), [Rule30EtherTrap.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherTrap.lean), [Rule30EtherTrapWidth20.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherTrapWidth20.lean), [Rule30EtherThreeTrap.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean), [Rule30EtherThreeReach.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherThreeReach.lean); `research/verify-p4traps-rigor/P4Traps.lean`.
- **AI.** Agents found the traps with C searches. Two round-2 agents independently refuted the round-1 claim that every finite right half enters a single trap.
- **Proved.**
  - Closed, labelled traps of 109, 188 and 188 states for 0001, 0011 and 0111 (widths 16, 16 and 14).
  - The trap t001: 815 states, 47 cells, period 21.
  - `never_enters_*`: explicit finite right halves never enter the round-1 traps.
  - The pure ether lies in no trap of width ≤ 20 (24 certificates).
- **Computed.**
  - Every true right half at onset times T ≤ 300,000 enters its trap, with maximum delays 1017, 1869 and 829.
  - All 18,258 runs for 001 enter t001.
  - 0101 is absorbed in about 3% of runs; 011 never is.
- **Forms.** `eventual-word` for least period 4 and the word 001, through Absorption (a project reduction); `coupled-halves`, whose right-half relaxation Absorption is.
- **Idea.** A trap is a set of strip states closed under every far input on which column 1 at white phases is a fixed function of a time label. A periodic tail never enters it, so entry excludes the tail.
- **Transfer.** Absorption(0111) has one alignment, no skeleton and the shortest delays (S5).
- **Obstacle.**
  - This is a nucleation theorem for a chaotic driven half-line.
  - Entry happens before any signal from the right edge can arrive.
  - Paths that avoid the trap keep the full growth rate (computed). No barrier is proved for Absorption, and nobody has checked whether B7's argument against additive potentials extends to it.
- **Artifacts.** The Lean files above; [research/B-edge-trap/](research/B-edge-trap/), [research/p3-ether/](research/p3-ether/).

#### F4. Ethers and walls
*Promise: medium. Verification: Lean (ours); the census is computed.*
- **Origin.** 2026-10-15. Round 2 (p4-edge agent) and the final batch: [Rule30Ether.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Ether.lean), [Rule30EtherThree.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherThree.lean), [Rule30EtherThreeNoWall.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherThreeNoWall.lean), [Rule30PeriodTwoCoupled.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoCoupled.lean).
- **AI.** Discovered by an agent analysing why period-4 traps exist. A verifier narrowed an overstated "no wall exists" to widths ≤ 12 (Lean) and ≤ 28 (search).
- **Proved.**
  - `ether_rule`: the 7×4 ether carries 0001, 0011, 0111 and 0101.
  - The 13-cell wall W109 (`wallOK_true`); `ether_wall_trap`.
  - A 12×3 ether for 001 and 011. No period-3 wall of width ≤ 12 (Lean), or ≤ 28 (search).
  - `ether_coupled_witness`: the ether is an infinite configuration meeting every period-2 constraint.
- **Census (computed).** Small ethers also carry 01011, 00001, 01111 and 15 words of period 7.
- **Forms.** `eventual-word` for periods 2–4 (conditional exclusions), and words of periods 5 and 7 through the census.
- **Idea.** Periodic backgrounds whose columns carry the period words, plus closed walls, explain every trap found.
- **Transfer.** This is the vocabulary for nucleation: Absorption(w) says every finite right half eventually builds an ether segment plus a wall.
- **Obstacle.** The ether is also the counter-witness for local methods (JointBarrier) and the likely witness of a CQ01 lasso (D9, D12).
- **Artifacts.** The Lean files above; [research/B-edge-trap/](research/B-edge-trap/).

#### F5. The zero-boundary left half Θ
*Promise: medium as a map. Verification: Lean (ours). Details in D3.*
- **Origin.** 2026-10-15. Round 2, three independent formalisations merged into [Rule30ZeroBoundary.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean).
- **AI.** Three agents formalised the same object in three encodings without coordination; an integration agent merged them.
- **Proved.** Θ, `two_step_shift`, `Q01_iff_Theta`, `Q01_iff_bounded`, `count_constrained`, `backward_det`, `free_bits_no00_no11111`.
- **Forms.** `eventual-word` for the word 01, through Q01 and CQ01.
- **Idea.** The column next to the wall determines the whole ZBL history, and every column sequence occurs exactly once.
- **Transfer.** The analogue of Q-tilde's parity split (F10), but with no finite description.
- **Obstacle.** Θ looks random beyond depth about 15 (D3).
- **Artifacts.** The Lean file above.

#### F6. Epochs, stripe absorption, deviation-front odometer
*Promise: low. Verification: Lean (ours).*
- **Origin.** 2026-10-15. Round 2 and the final batch: [Rule30ZeroBoundaryStripe.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripe.lean), [Rule30ZeroBoundaryStripeFront.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripeFront.lean), [Rule30ZeroBoundaryStripeFamily.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripeFamily.lean).
- **AI.** The synthesis agent noticed that one agent's stripe-absorption theorem proved another agent's open conjecture; a verifier corrected a phase convention.
- **Proved.**
  - Epoch decomposition: a history dies iff some epoch has odd length.
  - `stripe_absorb`, `Theta_eventually_stripe_iff`.
  - `stripe_prefix_family_list` (|v| ≤ 3 kernel-checked; |v| ≤ 7 computed).
- **Forms.** `eventual-word` for the word 01, through Q01 on special classes of rows.
- **Idea.** Track the first deviation from the stripe; it moves one cell toward the wall per step.
- **Transfer.** Epochs are the formal analogue of Q-tilde's arches. Front positions are max-plus quantities, consistent with B7.
- **Obstacle.** Two zeros in f already interact over depths [12, 84].
- **Artifacts.** The Lean files above; [research/A-invsearch/](research/A-invsearch/).

#### F7. Bit-sliced kernel checkers and packed-Nat certificates
*Promise: low; infrastructure. Verification: Lean (ours).*
- **Origin.** 2026-10-15. Final batch and round 1: [Rule30ZeroBoundaryLanes.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryLanes.lean), [Rule30ZeroBoundaryWidth52.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryWidth52.lean), [Rule30FactorWindow.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30FactorWindow.lean), [Rule30Window.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Window.lean).
- **AI.** An agent replaced a per-path kernel DFS by a bit-sliced lane checker and proved it sound; a verifier rebuilt all source files in its own build directory.
- **Proved.**
  - `q01_of_chunks`, with 2^18 lanes per Nat.
  - `q01_width_le_52` (about 80 s); W ≤ 56 in the archive (about 345 s).
  - `transient_add_period_ge`, `no_small_eventual_period`.
  - No `native_decide` and no `bv_decide`.
- **Forms.** Finite instances of Q01; `morse-hedlund` and `finite-certificates` on a finite prefix (T + P ≥ 16359).
- **Idea.** Pack many independent cases into the bits of one natural number, so the kernel's fast Nat operations check them together.
- **Transfer.** The tool for kernel certificates of finite statements. It fits the short MFWs (the draft planned 2^17 lanes for L = 9). The long MFWs of D12 (L = 18 or 37) need 2^(2L−1) windows, which is infeasible; they go through kernel-only LRAT instead.
- **Obstacle.** Cost grows exponentially with width.
- **Artifacts.** The Lean files above; [research/kernel-certify-r2/](research/kernel-certify-r2/).

#### F8. Barrier theorems
*Promise: none; they are filters. Verification: Lean (ours), plus C6 (computed) and B7 (derived).*
- **Origin.** 2026-10-15. Rounds 1–2 and the final batch: [Rule30Realization.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Realization.lean), [Rule30ZeroBoundaryBarriers.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryBarriers.lean), [Rule30ZeroBoundary.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean), [Rule30DrivenLeft.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30DrivenLeft.lean), [Rule30EtherTrap.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherTrap.lean).
- **AI.** Each barrier came from an agent whose attack failed and which then proved why; verifiers delimited the scope.
- **Proved.** `Rule30Realization.barrier`, `column_realizable_unique`, B1, B2, B6, JointBarrier, `edge_region_barrier`, `barrier_exists`/`barrier_unique`, and `word_lemma`; plus C6 (computed), the local obstruction (computed) and B7 (derived).
- **Scope.**
  - B1, B2 and B6 cover Q01 only.
  - JointBarrier is the only proved two-sided barrier; it covers local rankings at centre flips. B7's two-sided variant (derived) adds additive rankings in that setting.
  - A lasso barrier for CQ01 along c7 truncations is conjectured, not proved (D9).
  - No barrier is known for Absorption.
- **Forms.** All forms; the F-OR barrier especially hits the `series-f2-lfsr`, `two-adic` and `cobham-christol` arguments, which rules 90, 150 and 210 share.
- **Idea.** Exhibit a configuration (often infinite) that satisfies everything a method uses yet has the wrong answer.
- **Transfer.** Screen every external technique against §0.5 before investing in it.
- **Obstacle.** None.
- **Artifacts.** The Lean files above; [research/A-invsearch/lean/](research/A-invsearch/lean/) (`JointBarrier.lean`, `ZBLBarrier.lean`, `ZBLEdgeDFA.lean`).

#### F9. Jen with a clock
*Promise: low. Verification: Lean (ours). The same result is placego's Theorem A, whose `TheoremA.lean` we did not rebuild.*
- **Origin.** 2026-10-15. Round 2 ([Rule30ZeroBoundary.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30ZeroBoundary.lean)); placego [PERIOD-TWO.md](https://github.com/ghywel/placego/blob/main/PERIOD-TWO.md) §2 and [TheoremA.lean](https://github.com/ghywel/placego/blob/main/tests/probes/lean/TheoremA.lean) (2026-10-05/09; Claude Local with GPT second reads).
- **AI.** Agents on both sides.
- **Proved.**
  - `jen_clock`: l + 2 ≤ T + m + 2P.
  - `free_bits_clock`, `alternating_right_col1_clock`.
  - placego's Theorem A: b ≤ 2a + L + 2P − 1. Its Theorem B: no zero run longer than 2P − 2 in the forced left half.
- **Forms.** `eventual-word` for the word 01, through a finitary right-half statement; effective versions of `series-f2-lfsr` and `base-b-irrational` on windows.
- **Idea.** Jen's theorem, made quantitative: a periodic window of two adjacent columns cannot be longer than a bound fixed by its start and its period.
- **Transfer.** A near-perfect linear-complexity profile, |L(n) − n/2| ≤ K, bounds periodic windows by l ≤ T + 2P + 2K − 1. That is the clock inequality with 2K in place of m. For c, the data give K ≤ 9.5 for n ≤ 10⁶.
- **Obstacle.** It does not use the OR, and the clock interface needs zero-entropy windows.
- **Artifacts.** Ours as above; placego (no licence).

#### F10. Hidden slowness and exact-fit interleaving (Q-tilde, OEIS A394051)
*Promise: low; methodological. Verification: Lean (ours; 1,436 lines; standard axioms re-printed).*
- **Origin.** [VibeProof/HofstadterQ/lean](../HofstadterQ/lean/) (2026-10-15), formalising B. Cloitre, [arXiv 2604.06237](https://arxiv.org/abs/2604.06237) (v3 2026-07-22). Independent proof by M. Mantovanelli, [arXiv 2603.29622](https://arxiv.org/abs/2603.29622).
- **AI.** Cloitre's v3 PDF says ChatGPT 5.5 and 5.6 were used for editing, organisation and exploratory computation. Mantovanelli's v3 declares ChatGPT use and says his v2 finite-state closure "left a semantic gap". Our Lean was written with Claude Code in one session.
- **Proved.** `QTilde.qtilde_wellDefined`, `isQTilde_unique`, `Qt_bounds`.
- **Forms.** No rule-30 form directly; methodological for the period-2 left problem and the word forms.
- **Idea.** A sequence with a hidden zero-entropy structure can be generated level by level by exact interleaving laws, and totality becomes one finite identity per level.
- **Transfer.** A two-tape interleaving-machine library for machine-checking any proposed morphic description, for example of the block law (F11).
- **Obstacle.** Zero entropy made Q-tilde provable. Every rule-30 constrained system we measured has positive entropy, except the boundary layers, and those already have exact descriptions (F6, F12).
- **Artifacts.** The QTilde Lean files.

#### F11. The period-2 block law
*Promise: medium. Verification: computed (two codes, six runs). The Lean partial laws are now implied by the light-cone language (D2).*
- **Origin.** 2026-10-15. The round-2 synthesis measurement ([research/synth-r2/](research/synth-r2/)), cross-validated by an independent code in the write-up phase; partial Lean laws in [Rule30PeriodTwoWidth5.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoWidth5.lean) and [Rule30PeriodTwoWidth6.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoWidth6.lean).
- **AI.** Found by the synthesis agent; re-implemented and re-analysed by later agents.
- **Computed.**
  - After at most 27 samples, every gap between ones of u is 3 or 5, every 100 is isolated, and the density is 3/14.
  - Factor counts p(64) = 702 and p(128) = 15,960.
  - The law is not strip-local, and it fails for infinite right halves: the ether gives gap 2.
  - Re-analysis shows a random renewal process with about 2 bits per 100-block.
- **Forms.** `eventual-word` for the word 01, through CQ01.
- **Idea.** A rigid local grammar for column 1 beside a 0101 centre.
- **Transfer.**
  - Under the law, every epoch depth would lie in {6, 10}.
  - A left search under the law reportedly killed every start of width ≤ 196. Its output was not saved, so this is unverified.
  - D12 is the exact version of this filter.
- **Obstacle.** About 0.07 bits per white time of entropy remains. Proving the law is itself an Absorption-type statement.
- **Artifacts.** As above.

#### F12. Power-of-two right-diagonal periods
*Promise: low. Verification: Lean (ours).*
- **Origin.** 2026-10-15. [Rule30Diagonals.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Diagonals.lean), [Rule30RightPeriods.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30RightPeriods.lean); reproves and extends E. S. Rowland, [Complex Systems 16(3) (2006)](https://www.complex-systems.com/abstracts/v16_i03_a04/).
- **AI.** An agent found and proved the structure theory, and refuted its own guessed lower bound with kernel-checked counterexamples.
- **Proved.** `e_step`, `rows_at_powers_of_two`, `restart`, `center_black_lt` (c(t) = 1 ⇒ 2^(e_t) > t), `no_three`. That the right-diagonal periods are unbounded is older: Gravner and Griffeath, Theoret. Comput. Sci. 466 (2012) 64–86, Prop. 3.3.
- **Forms.** `diagonal-array` and `nks-integer-rows` (stated in CATALOG.md); vocabulary only for `two-adic` and `cobham-christol`, which F-OR bars.
- **Idea.** The period of each right diagonal doubles exactly when one cell is black.
- **Transfer.** None for c.
- **Obstacle.** Rules 60, 90, 150 and 210 share all of it, and it never reaches the centre.
- **Artifacts.** The Lean files above; [research/diagonal/](research/diagonal/).

#### F13. Skeletons and bad-class language certificates
*Promise: low. Verification: Lean (ours).*
- **Origin.** 2026-10-15. Rounds 1–2 and the final batch: [Rule30PeriodFourSkeleton.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean), [Rule30EtherThreeSkeleton.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30EtherThreeSkeleton.lean), [Rule30PeriodTwoLanguage.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoLanguage.lean), [Rule30PeriodTwoWidth5.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoWidth5.lean), [Rule30PeriodTwoWidth6.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoWidth6.lean).
- **AI.** Agents computed the bad components and exported certificates; a verifier recomputed them.
- **Proved.**
  - `Cert.sound_bad`.
  - The period-2 skeleton: column −1 is black at the black times, the free bits never contain 00, and column −4 is white at the white times.
  - The width-5 and width-6 laws.
  - Skeletons for 0001, 0011, 001 and 011.
- **Computed.** Growth rates of 1.32, 1.29 and 1.275 per period for 0001, 0011 and 0111.
- **Forms.** `eventual-word` for periods 2–4, each reduced to a left problem with a restricted free-bit language.
- **Idea.** If c is eventually w-periodic, the true strip eventually stays in an exempt class, so anything true on that class holds eventually.
- **Transfer.** For period 2, the exact light-cone language implies the width-5 and width-6 laws (Appendix B.2), so prefer it.
- **Obstacle.** The restricted languages still grow, so no finite description follows.
- **Artifacts.** The Lean files above; [research/progB-avoid/](research/progB-avoid/).

#### F14. The nine-black shield and black-run families
*Promise: low. Verification: Lean (ours).*
- **Origin.** 2026-10-15. Round 1: [Rule30BlackRuns.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30BlackRuns.lean), [Rule30BlackRunBlocks.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30BlackRunBlocks.lean).
- **AI.** Found independently by two agents; each theorem had rigour, re-derivation and counterexample verifiers.
- **Proved.**
  - `nine_black` (optimal) and `black_shield`.
  - Every word with a white cell whose cyclic black runs are all ≥ 9 is excluded.
  - Theorems B, B′ and D.
  - 0^r 11 for r = 6 and r ≥ 10.
- **Forms.** `eventual-word`: infinite families of excluded words.
- **Idea.** Nine black steps in a column write a fixed pattern to its right; long black runs therefore force a contradiction with masked Jen.
- **Transfer.** Every nonconstant eventual period word has a black run of length ≤ 8 followed by a white cell. The argument uses the OR but is local. Part of the census in S3.
- **Obstacle.** Local; short words are out of reach.
- **Artifacts.** The Lean files above.

#### F15. Direct certificates for the F₂ and Morse–Hedlund forms
*Promise: low. Verification: Lean (ours) for the first item; data for the rest.*
- **Origin.** 2026-10-15. [Rule30Window.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30Window.lean), [Rule30FactorWindow.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30FactorWindow.lean), [research/gf2-algebra/](research/gf2-algebra/), [research/complexity/](research/complexity/).
- **AI.** Agents wrote the certificates and analyses; a verifier refuted one agent's claim that every word of length ≤ 20 occurs in the first 10⁷ bits.
- **Proved and measured.**
  - Lean: T + P ≥ 16359.
  - Berlekamp–Massey gives T + P ≥ 499,998.
  - All length-44 windows of the first 10⁷ bits are distinct, which gives T + P ≥ 9,999,957 if the data file is right.
  - 2^20 − 96 distinct length-20 factors occur in the first 10⁷ bits. So the true factor complexity satisfies only p_c(20) ≥ 2^20 − 96; the draft's "p_c(20) = 2^20 − 96" was wrong.
  - 2-kernel words are distinct up to K = 13.
  - Paper: rule 30's t-step centre map has ANF degree exactly 2t − 1. Degree carries no information: all 34 elementary rules of maximal degree (2t + 1, checked at t = 7) have eventually periodic single-seed centres.
- **Forms.** `series-f2-lfsr`, `morse-hedlund`, `finite-certificates`; `cobham-christol` (2-kernel data only).
- **Idea.** Turn finite data into kernel-checked lower bounds on T + P.
- **Transfer.** None beyond larger finite bounds.
- **Obstacle.** Finite windows cannot settle an eventual statement.
- **Artifacts.** As above. The 10⁷-bit centre file lives outside the repository.

#### F16. The adversarial multi-agent workflow
*Promise: low; a method, not mathematics. Verification: process record.*
- **Origin.** 2026-10-15. [research/workflows/](research/workflows/) and [research/results/](research/results/).
- **AI.** Entirely AI-run under human direction.
- **Scale.** About 100 Claude Code agents produced 393 indexed theorems; 5,353 constants were checked with 0 axiom violations.
- **Verifiers caught:**
  - an off-by-one (refuted in Lean);
  - the claim that every word of length ≤ 20 occurs in the first 10⁷ bits (96 words of length 20 are absent there);
  - `bv_decide` files that trust compiled code;
  - an overstated "no wall" claim;
  - the Q01-only scope of B1, B2 and B6.
- **Forms.** All (method).
- **Idea.** Attack, then attack the attack, and accept only kernel-checked results.
- **Transfer.** Reuse for any new campaign; the barriers and verifiers are the reusable part.
- **Obstacle.** It finds errors; it does not supply ideas.
- **Artifacts.** Prompts and outputs in the folders above.

---

## 3. Ranked shortlist

**Order:** the audit's revised salvage order first (S1–S4), then the remaining items of the draft in their original relative order (S5–S8), then the demoted item (S9). The ranking criterion is expected progress toward Problem 1 or an equivalent form per unit of effort; partial exclusions and new attack surfaces count.

**Constraints:**
- Laptop runs ≤ 60 s, wrapped in `timeout 60`.
- Lean 4.30.0 with Mathlib `c5ea003`, through the library's lake project. A probe file importing Mathlib compiles in about 11 s with `lake env lean`.
- No `native_decide`, no `bv_decide`, no `ofReduceBool`.
- Prime Intellect pods only with the user's approval.

Paths used below:

```
P=/Users/swish/.claude/jobs/b8cd2926/tmp/r30tech        # scratch; copy what you keep into research/
A=$P/audit                                              # the audit's scripts and data
R=/Users/swish/src/wolfram/vibe-proof/VibeProof/Rule30Prize
E=$R/equivalents
```

**Prerequisite (not ranked): verification hygiene (E6).** Run `cd $E && timeout 60 lake env lean scripts/CheckAxioms.lean`. Plan a replay under the installed v4.35.0 toolchain, with Comparator and nanoda. Add `run_cmd`, `addDecl` and `debug.skipKernelTC` to the source scan.

### S1 (medium). Exact light-cone realizability for CQ01, with kernel-only LRAT import (D12, D2, D3, F2, F5)
**Why.**
- Period 2 is the next open case, and three groups converged on the same object.
- Exact realizability sees constraints of every length; short MFW lists do not. The extremal survivors of the 19-MFW filter die much earlier under it (W = 96: by time 87 at the latest; the best at about 57).
- It computes the exact coupled lifetimes D_exact(W), which is what a proof of CQ01 must bound.

**First experiments** (measured on the laptop):
```
L=$(grep -m1 '^LEAF 116' $A/leaves96.txt | awk '{print substr($3,1,96)}')
timeout 60 python3 -I $A/scripts/realize.py "$L"      # 1.1 s: |u| = 58, longest realizable prefix 28, death by about 57 (not 116)
timeout 60 python3 -I $A/scripts/exact_deaths.py $A/leaves96.txt 96 0 26     # about 1.2 s per leaf; first 10 leaves: max 85
timeout 60 python3 -I $A/scripts/exact_deaths.py $A/leaves96.txt 96 26 52
timeout 60 python3 -I $A/scripts/exact_deaths.py $A/leaves96.txt 96 52 78
timeout 60 python3 -I $A/scripts/exact_deaths.py $A/leaves96.txt 96 78 103   # audit result over all 103 leaves: every leaf dies by 87
cc -O3 -o /tmp/ulang16 $A/scripts/ulang_indep.c && timeout 60 /tmp/ulang16 16   # 32 s: counts up to 316, two new MFWs at L = 16
```
Then build a DFS that checks exact realizability incrementally (z3's incremental solver, keyed on u-prefixes) and computes D_exact(W) for growing W within the laptop limit. Record every MFW from the UNSAT cores, as `minforb.py` does for one start at a time.

**Lean step.**
1. State CQ01 at bounded left width and the light-cone realizability predicate (extending [Rule30PeriodTwoLanguage.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/lean/Ruliology/CellularAutomata/Rule30PeriodTwoLanguage.lean)).
2. Build or find an LRAT/RUP checker proved sound in Lean that the kernel can evaluate with `decide` on packed-Nat clause tables, in the style of `Rule30ZeroBoundaryLanes`. Start with the length-18 MFW (a cone of 35 cells).
3. Prove each harvested MFW forbidden by a kernel-replayed certificate.

**Continue/kill.**
- S1 is a measuring tool first. Linear lifetimes alone do not rule out a proof: Q01's D(W) is already about 1.8W, and ether truncations give D_exact(W) − W ≈ 0. So the growth of D_exact(W) − W is not a kill signal by itself.
- Continue as a proof route while the harvested MFWs show structure that an all-widths argument could use: families indexed by length, a regular language of MFWs, or a bounded set of shapes.
- Stop treating it as a proof route if, as W grows, new MFWs keep appearing with no recognizable families, so that their counts and shapes behave like a random-constraint model. Keep it then only for the counterexample-first tests of S8.
- Never kill on a plateau of excess/W at short MFW length.

### S2 (medium, library). Axiom-free CC0 equivalences (A1, B3, A5, A2, B4, C3, C10)
**Why.** These are certain wins for the library. The Stanley engine turns `p-recursive` and `fatou` into theorems and also proves that holonomic methods cannot apply to f.

**Already done in our library:** Kronecker–Hankel ([LinearRelations.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/LinearRelations.lean)), the 2-adic forms by re-derivation ([TwoAdic.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/TwoAdic.lean)), Morse–Hedlund ([ShiftOrbit.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/ShiftOrbit.lean)) and the register form of `nlfsr` ([WordsAutomata.lean](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/Rule30Equivalents/WordsAutomata.lean)).

**First experiment.** Write a stub file and compile it with `cd $E && timeout 60 lake env lean <stub>.lean` (about 12 s). It holds these statements, each with `sorry`:
- `p-recursive`: CATALOG.md's `problem1_iff_not_pRecursive`;
- `fatou`: CATALOG.md's `problem1_iff_transcendental_Q`;
- reflection complexity: Problem 1 iff r_c(n) ≥ 1 + ⌊(n+1)/2⌋ for all n ≥ 1;
- the complexity-profile wording of `nlfsr`.

**Port.**
- Port only the Ceiling-Orbits files `RB/EventuallyPeriodic.lean`, `CITED/Stanley.lean` and `CITED/StanleyProof.lean`, whose import closures are axiom-free (table in A1). Re-type and review rather than copy blindly.
- First grep them for `#eval`, `run_cmd`, `initialize` and `axiom`, because Lean files can run code at elaboration. Check `#print axioms` after porting.
- Never import `B3/DigitPeriodicity.lean`, `BL/*`, `AB/*`, `RB/GeneralBase.lean`, or Transcendence-Criteria's `CITED/Stanley.lean` and `RB/EventuallyPeriodic.lean`.
- Mathlib gap: `PowerSeries.coeff_iterate_derivative` is absent from `c5ea003`.

### S3 (medium, partial results). A word-exclusion census across three engines (C1, F7, F14, E11)
**Why.** These exclusions are unconditional, cover all finite seeds and are cheap. Running the three engines together maps exactly where local methods end, and they complement each other: 0^7 1 is certified by Berzai's engine but not by ours. The Equational Theories Project (E11) is the template for running such a census with a public table of open cases.

**First experiment** (measured times):
```
cd $R/research/generalize-jen
timeout 60 python3 -I strip_scan.py 8 12 12      # all Lyndon words of length 8-12, width <= 12; about 2 s
timeout 60 python3 -I certgen.py 00000011 00000001
```
Compare the output with placego's 24 words of period 10–14 and with Berzai's lists. Re-implement Berzai's "#edges = #vertices" component criterion, which reaches 0^7 1.

**Lean step.** Extend `Rule30StripCertificateTable`, and re-prove the q-uniform families 0 1^q (q ≥ 9) and 1 0^q (q ≥ 10) by hand.

### S4 (low, long shot). The Duhamel–Cartier route, gated by controls (B1, B2, A8, B5)
**Why.** It is the only global algebraic handle outside the local barriers, and it targets non-automaticity, which implies Problem 1. The audit lowered it from medium: passing the rule-90 firewall is necessary but not sufficient.

**First experiment.**
1. `timeout 60 python3 -I $P/portfolio/scripts/duhamel_check.py 160` (verified for rule 30).
2. Adapt the script to rule 54 (source l ∧ r) and confirm that the same decomposition holds while the centre is (1100)^∞.
3. Compute Cartier images Λ₀ and Λ₁ of the source data down to decimation depth 8 for rules 30 and 54 and for c7, and track candidate invariants (degree of the chiral source, support size). Discard any invariant that behaves the same on rule 54 or on c7.

**Lean step.** Formalise rule 30 = rule 150 ⊕ (c ∧ r) and the Duhamel identity with Finset sums over ZMod 2, by induction on t, with small t checked by `decide`.

**Kill.** Park the route if every candidate invariant stays bounded on the first 2^12 kernel elements, or fails to separate rule 30 from rule 54 and from c7. No finite census can decide it anyway.

### S5 (medium, partial target). Absorption(0111) (F3, F4)
**Why.** It has one alignment, no skeleton, and delays ≤ 829 in 282,144 runs. Proving it would exclude the tail 0111.

**First experiment.**
1. Compute the *input-forced basin* of the 188-state, width-14 trap: the strip states from which every far-input sequence enters the trap within k ≤ 64 steps. That is 4 phases × 2^14 states, a backward attractor computation taking under a second.
2. For 10³ random finite right halves with support ≤ 64, record the time of the first basin visit against the entry time. Adapt `$R/research/B-edge-trap/entry.c` and `$R/research/verify-p4traps-rigor/{check_trap.py,sim_check.py}`; the whole run stays under 60 s.

**Lean step.** The basin's closure is a finite check by kernel decide, like `wallOK_true`.

**Continue/kill.**
- If entry is always preceded by a short forced phase, Absorption(0111) reduces to an occurrence statement about a set of local states.
- If the basin is tiny or is hit only at entry, there is no precursor structure.
- No barrier is proved for Absorption. Before searching for potentials, check whether B7's argument extends to the driven right half; look first at front-type (max-plus) quantities and learned global rankings (D13).

### S6 (medium, infrastructure). Seed-free foundations: Jen and period 1 for every nonzero finite configuration (D1, F1)
**Why.**
- Condrey's corollary follows from our 10-line `no_column_eventually_constant` once `Rule30Jen.not_adjacent` holds for every finite configuration, or for every number-like one as in Kopra.
- S1–S3 need this whenever they pass to Fᵀ(seed).
- placego's Proposition 20 makes seed-free theorems strictly stronger.

**First experiment.**
1. Find where `Rule30Jen.cell` enters `not_adjacent`, and state the version over finitely supported initial rows `Int → Bool` with `sorry`.
2. Run a C check over all 65,535 nonzero rows of width ≤ 16 for 256 steps (under 10 s): no column in the light cone is constant on [128, 256).

**Lean step.** Port the proof, then add Condrey's sharp horizon w + 2 as a finitary lemma. It is proved in the paper but not formalised in the foundry. H(2, w) ≥ w is only a sketch in the paper; do not rely on it.

### S7 (filter). Barrier-first screening (D8, D9, D13, F8)
**Why.** Closing certificate families formally sends effort elsewhere. B7 is new and cheap, and extending C6 to rule 30⁴ covers 2-step lexicographic rankings. The c7-truncation lasso for CQ01 is **a conjecture to prove**, not a known barrier.

**First experiment.**
1. Adapt `$R/research/A-invsearch/conslaw2.py` to rule 30⁴ at range ≤ 6, sized to run under 60 s.
2. Encode the all-width ranking conditions with de Bruijn potentials as an LP for r ≤ 4 (glpsol is installed), and confirm it is infeasible. The bounded-width LP (Appendix B.6) is vacuous.
3. Write the statement of a CQ01 lasso barrier along c7 truncations, modelled on `finite_abstraction_has_lasso`, and test it on the D12 survivors.

**Lean step.** State B7 for small r; Hedlund balance for rule 30² is a finite check for each range. Attempt the CQ01 lasso theorem.

### S8 (risk reduction). Counterexample-first tests of the open sub-hypotheses (E2, E3, E10, D10)
**Targets:**
- D(W) ≤ 2W + 8 beyond W = 71;
- C3w(011);
- period-3 walls wider than 28;
- t001 traps of width 23–46;
- the foundry's L4, on the survivors from S1;
- any proposed CQ01 lifetime bound, scored by exact death (D12).

**First experiment.**
- Randomised restarts of `dfs_lang` (with `use_lang = 0`) on random prefixes at W = 80–100, recording the best survival per width.
- A z3 query (installed) for "a trap of width 23 for 001", under `timeout 60`.
- Beyond the exhaustive widths (W > 150), PatternBoost-style search (E10) scored by exact coupled death.

**Value.** Each refutation saves a dead reduction. Rounds 1 and 2 already lost the C3 off-by-one, the single-trap claim, and the claim that every word of length ≤ 20 occurs in the first 10⁷ bits.

### S9 (demoted). The short-MFW right-half filter (D2; the draft's S1)
**What it was.** Define Q01_lang with the exact light-cone language, extend the MFW list by length, port the MFWs by bit-sliced kernel checks, and continue while excess/W falls as L grows.

**Why demoted** (audit, confirmed in D2 and D12):
- The language has MFWs of length 18 and 37 and is very unlikely to be a shift of finite type, so a finite list of short MFWs misses most of the constraint.
- The extremal filtered survivors die far earlier under exact realizability (116 → about 57 at W = 96; 151 → about 99 at W = 128), and the two L = 16 MFWs change none of the filtered maxima at W = 56, 96 and 128.
- A plateau of excess/W at short L is an artefact, so the draft's kill rule was wrong.
- Bit-sliced kernel checks over 2^(2L−1) windows are infeasible at L = 18 or 37.

**What is kept.** The counts and MFWs up to L = 16, the subsumption of the Width5/6 laws, and Q01_lang as a Lean statement (Q01 ⇒ Q01_lang ⇒ CQ01). S1 replaces the rest.

---

## 4. What not to repeat

### 4.1 Proof shapes the barriers exclude, and how firmly

| Shape | Why it fails | Status of the reason |
|---|---|---|
| Finite-state certificates for **Q01**: regular closed sets, n-gram/CPS/FAR, finite abstractions with rankings | Every finite abstraction has a reachable lasso along truncated stripes | Lean: B1, B6 (Q01 only) |
| The same for **CQ01** | A lasso along c7 truncations is expected | **Conjecture** (D9); not proved |
| The same for **Absorption** | None known; trap-avoiding strip paths keep the full growth rate | Computed only; **no barrier** |
| Strip certificates for short words | Strip graphs of primitive words of length 2–7 contain components whose white-phase outputs do not commute | Computed (width ≤ 16; ≤ 20 for 0001); Lean `word_lemma` for the ether; Berzai's boundary theorem; Stephan's Theorem D as cited by placego |
| Rankings through (width, wall window, edge window) for Q01 | Truncated stripes | Lean: B2 |
| Local rankings that decrease at every flip of the centre (two-sided) | Truncations of c7 | Lean: JointBarrier |
| Additive potentials: pattern counts, potentials fitted by LP, BBB(4)-style counts, polynomial matrix interpretations | Over a random bulk the change has mean zero, which forces a conservation law, and none exists at range ≤ 8 | Derived (B7) for Q01 and for centre flips; C6 computed; not checked for Absorption |
| Ranking LPs over rows of bounded width | Vacuous: V = C − width always works | Appendix B.6 |
| Arguments using only left-permutivity, the light-cone edge, power-of-two diagonal periods, the odometer, Lucas or F₂-linearity, ANF degree, or dilation identities | They hold for rules 90, 150 and 210, whose centres are eventually periodic; ANF degree, prediction rank, a perfect linear-complexity profile and Conjecture H also fail on rules 22, 54, 126 and 60 | Lean: F-OR; B5 controls |
| An invariant of the Duhamel–Cartier orbit that does not see the chirality of the source or the finiteness of the seed | Rule 54 has the same structure and c7 the same recursion, both with periodic centres | Computed (B1) |
| Left-only statements that ignore the finiteness of the right half | Q01-only witnesses; for rule 210 the left-only statement is false although period 2 is excluded | Scope of B1, B2, B6; D5 |
| Edge structure plus windows shorter than the wall distance; backward reasoning; preimage trees | Every far part can be completed at will, and every column is realised | Lean: `edge_region_barrier`, `barrier_exists`/`barrier_unique`, `column_realizable_unique` |
| Finite windows, SAT bounds or a census offered as proofs of eventual statements | Finite rows fake periodic prefixes for about 1.25–1.9 times their radius; Condrey's H(2, w) ≥ w points the same way but is only a sketch | Computed (F15, D10) |
| Zero-entropy interface exclusions (Sturmian, rotation, substitutive) used as the final step | The real interface has positive entropy | Measured (C2) |
| A single trap per word; low-complexity descriptions of the right half; simple monovariants | Refuted in rounds 1–2 | F3; write-up §8 |
| Extending strip-relaxation laws for period 2 | Superseded: the exact light-cone language implies them | Appendix B.2 |
| Growing a short MFW list as the main period-2 route | The language has MFWs of length 18 and 37; the short-L plateau is an artefact | Audit (D2, S9) |

### 4.2 Routes closed by the literature or by controls
- **Holonomic or analytic irrationality** on f = Σ c(t)zᵗ (Apéry, conservative matrix fields, G-functions, holonomy bounds, determinant methods): f is D-finite iff Problem 1 fails (A1).
- **Mahler, Adamczewski–Bugeaud and Subspace dichotomies:** they say nothing about the rational case (A9), even with Roth now reported in Lean.
- **Liouville and tail decay on 0/1 digits:** the margin is zero (A3).
- **Measure-level, ergodic, mutual-information and ground-state statements:** the single seed is invisible to them (Howe; Condrey's roundtable; Berzai; D14).
- **Automatic-sequence, Walnut, number-wall or 2-kernel census certificates for c itself:** c needs ≥ 8,191 states, and every finite word extends to an automatic sequence.
- **Common errors in claimed proofs:**
  - Diagonal-period growth taken as evidence of aperiodicity; rule 90's Pascal diagonals grow too (Ulrey).
  - C(y)² = C(y²) misread as decimation (Topal).
  - Shortcut formulas for c: azhar's agrees with c 49.5% of the time; the c(t) = [t ∈ S_{t+1}] formula of arXiv 2604.00165 agrees 21/35.
  - Transferring the rule-210 clearing front to rule 30 (D5).
- **Counting-law measurements taken as a mechanism:** the law also holds for random centre words (D4).
- **Proxies that prove nothing about Problem 1:** density ½, a perfect linear-complexity profile, maximal ANF degree, prediction rank, and Conjecture H (B5).
- **Square-free binary sequences (TLMC #1243):** impossible for length ≥ 4, and unrelated to Problem 1.

### 4.3 Process failures to avoid
- **Accepting an AI-written uniform step without an independent second reading:** cochon123's Lemma F; Shallit's v1 gap; Mantovanelli's v2 closure gap.
- **Trusting "solved" tags without auditing statement fidelity:** A6697, #5226, A379240, #263, and Aletheia's vacuous "correct" answers.
- **Mixing up sources in AI-claim summaries:** the draft conflated First Proof batches 1 and 3, miscounted Aletheia's literature finds, cited Wachs's critique as Sun's paper, and called the audited ten proofs unreviewed (1.4).
- **Lean trust:**
  - Do not trust Lean results without a replay: v4.30.0 and several third-party toolchains predate the July 2026 kernel fixes (E6). Replay under v4.35.0.
  - Never use `native_decide`, `bv_decide`, `ofReduceBool` or metaprogrammed declarations; treat natively run LRAT checkers (PBLean, lrat-catcher) the same way.
  - Never import files that declare axioms or import them: Stephan's `AB/*`, `BL/*`, `B3/DigitPeriodicity.lean`, `RB/GeneralBase.lean`, and Transcendence-Criteria's `CITED/Stanley.lean` and `RB/EventuallyPeriodic.lean` (table in A1).
  - Lean files can execute code during elaboration, so scan downloads before compiling them.
- **Overstating barrier scope:** B1, B2 and B6 are Q01-only; say "conjectured" for CQ01 and "none known" for Absorption.
- **More broad swarms without a new global idea:** SW-01 kept 0 of 10 proposals (only 3 of them about rule 30), and our own synthesis agents put the odds of another round settling period 2 below 5%.
- **Copying code from repositories without a licence:** placego, rule30-foundry, cochon123, Dibujaron, avikj, eliottcassidy2000, beetree, ConwayTransducer.
- **Running long jobs on the laptop:** anything over a minute goes to a pod, with approval.

### 4.4 What a proof must look like (summary of the filters)
A proof must satisfy all of the following:
- use the OR;
- use the finiteness of the configuration in a way that no continuous (finite-memory or Cantor-continuous) reading can see;
- be non-local in space, and not additive at range ≤ 8;
- not rest on edge structure.

The candidate mechanisms that remain:
- an exact global description in special coordinates (Q-tilde style), though none has been found outside the boundary layers (D15 could settle this quickly);
- an invariant of the Duhamel–Cartier orbit that takes infinitely many values and separates rule 30 from rule 54 and from c7;
- front-type (max-plus) or learned global rankings (D13);
- counting arguments that exploit what is special about periodic centre words.

Exact realizability (D12) is the measuring tool for all of them in the period-2 case.

---

## Appendix A. Where the material is

All scratch paths are outside the repository; copy what you keep into `research/`.
- Survey downloads (untrusted, never executed) and survey scripts: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30tech/{rule30-projects,irrat-transc,words-automatic,bb-dynamics,frontier-ai,own-inventory}/`.
- Scripts and outputs of the draft: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30tech/portfolio/`.
  - `scripts/duhamel_check.py`, `scripts/subsume_check.py`, `scripts/additive_ranking_lp.py`;
  - `dfs/dfs_lang.c`, a copy of `research/progA-backdet/dfs.c` with a light-cone filter. Usage: `dfs_lang W MAXD use_lang n_mfw`;
  - `ulang15.txt`, `lean/Probe.lean`.
- The round-1 enumerator: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30tech/rule30-projects/scripts/ulang/ulang.c`.
- The audit: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30tech/audit/`.
  - `scripts/ulang_indep.c` (independent light-cone enumerator, L ≤ 16), `scripts/subsume_indep.py`, `scripts/dfs_lang21.c` (21 MFWs), `scripts/dfs_dump.c` (dumps DFS leaves), `scripts/realize.py`, `scripts/minforb.py`, `scripts/exact_deaths.py`, `scripts/check_realize.py`, `scripts/import_closure.py`, `scripts/eca_centres.py`;
  - `leaves96.txt` (the 103 W = 96 leaves with filtered death 110–116);
  - downloaded data in `dl_*` (untrusted, never executed).
- Raw survey cards, the draft and the audit: [research/technique-survey.json](research/equivalents-survey/technique-survey.json).
- Our archive: [../lean/](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/lean), [../research/](research/), [../writeup/rule30-state.html](writeup/rule30-state.html).
- The equivalent forms: [CATALOG.md](https://github.com/WolframInstitute/Rule30PrizeKit/blob/main/equivalents/CATALOG.md) and [Rule30Equivalents/](https://github.com/WolframInstitute/Rule30PrizeKit/tree/main/equivalents/Rule30Equivalents).

## Appendix B. Checks run (2026-10-15, laptop, every run under 60 s)

**Draft checks.**
1. **Light-cone u-language beyond L = 12.** The round-1 `ulang.c`, compiled with `cc -O3`, gives counts 2, 3, 5, 8, 12, 17, 25, 36, 50, 68, 91, 119, 156, 199, 251 for L = 1..15. The 12 foundry MFWs are reproduced, and seven new MFWs appear at L = 13–15 (listed in D2). L ≤ 15 takes 19 s with this code.
2. **Subsumption of our laws.** The nine kernel-checked words of `Rule30PeriodTwoWidth6.col1Forbidden` are 11, 00000, 100101, 10010001, 101001, 1010100001, 1010001001, 10010000101 and 1001000010001. Each is excluded at every position ≥ 1 by MFWs of length ≤ 13 (`subsume_check.py`).
3. **Left survival under the light-cone filter** (`dfs_lang.c`). The unfiltered run reproduces D(52) = 96, the bound of `q01_width_le_52`, and gives D(56) = 100.

   | W | no filter | {11} | {11, 00000} | 5 MFWs (L ≤ 9) | 19 MFWs (L ≤ 15) |
   |---|---|---|---|---|---|
   | 56 | 100 | 80 | 74 | 72 | 67 |
   | 96 | – | – | – | 122 | 116 |

   With all 19 MFWs: W = 40 → 47, 48 → 59, 64 → 82, 80 → 97, 112 → 134, 128 → 151, 136 → 160, 144 → 171 (24.7 s). At W = 96, using 9, 12, 14 and 19 MFWs gives 122, 120, 118 and 116. These maxima are artefacts of the short filter (checks 9–10).
4. **Duhamel identity.** c(t) = T_t(0) ⊕ Σ_{s<t} Σ_x T_{t−1−s}(x)·u^s_x·u^s_{x+1} holds for t ≤ 160, and T_m(0) = 1 for m ≤ 160. Central trinomial coefficients are odd, so rule 150's single-seed centre is all ones.
5. **Mathlib probe** (`lake env lean`, 11 s). `PowerSeries.coeff_iterate_derivative` is absent. `PowerSeries.derivative`, `Differential`, `PadicInt` and `Matrix.det` are present. `decide` confirms c(0..11) = 1,1,0,1,1,1,0,0,1,1,0,0.
6. **Naive ranking LP** (`additive_ranking_lp.py`, glpsol, r = 2). It is feasible for every W ≤ 16, because V = C − width works on rows of bounded width. This led to the all-width proof sketch of B7 (D8).
7. **Strip engines.** `strip_scan.py 8 12 12` runs in about 2 s and certifies no word of length 9. `certgen.py` finds no certificate for 0^7 1 at K ≤ 12, while Berzai's engine certifies it at K = 12.

**Audit checks.**

8. **Independent enumerator** (`ulang_indep.c`). It reproduces the counts and all 19 MFWs; L = 15 takes 7.9 s. L = 16 takes 32 s and gives count 316 and the MFWs 1000100001010001 and 0101000010000101. `subsume_indep.py` confirms check 2. `dfs_lang.c` reproduces 100 and 67 at W = 56, 116 at W = 96 and 151 at W = 128; with the two L = 16 MFWs (`dfs_lang21.c`) no maximum changes, and the multiplicity at W = 96 falls from 16 to 14.
9. **Exact realizability** (`realize.py`, z3 over the whole cone; cross-checked against the counts for L ≤ 8 and against every listed MFW). The best W = 96 survivor dies at about 57 through the MFW 010000101000010001; the best W = 128 survivor at about 99 through 1000010000100001000010100001010000100. All 103 W = 96 leaves with filtered death 110–116 die by 87 (`exact_deaths.py`), so D_exact(96) ∈ [87, 109]. At W = 56 the extremal u is realizable up to its kill: D_exact(56) = 67.
10. **Import closures** (`import_closure.py`, static, nothing compiled): the results in the table of A1.
11. **Controls** (`eca_centres.py`): rule 54's single-seed centre is (1100)^∞ for t < 400.
12. **Primary-source checks:** the corrections of Appendix C, plus confirmations of the formal-conjectures restatement, the foundry claims, Condrey's details, the bibliographic data of Kramer-Miller, Kopra, Natal–Al-saadi, Lairez–Storozhenko, Chen–Winterhof, reflection complexity and Tao–Teräväinen, the AlphaProof Nexus, OEIS Open and FrontierMath figures, the Jacobian counterexample, Knuth's note, the kernel-bug release versions, the Ceiling-Orbits theorem names and Comparator configuration, and most licences.

**Checks for this revision.**

13. Re-ran the import-closure scan on both Stephan repositories: same result as the audit; the `L90` files are also axiom-free. A grep finds `sorry` only inside comments of the axiom-free files, and no `#eval`, `run_cmd`, `initialize`, `addDecl`, `native_decide` or `implemented_by`.
14. Re-ran `realize.py` on the best W = 96 survivor (1.1 s; |u| = 58; longest realizable prefix 28) and `exact_deaths.py` on the first 10 leaves (12 s; maximum exact death 85).
15. Single-seed centres for t < 400: rule 54 is (1100)^∞, rule 22 is 1, 1, 0, 0, …, rule 90 is 1, 0, 0, …, rule 150 is all ones. Rule 167 coincides with rule 165 = ¬(l ⊕ r) from time 1 for 300 steps.
16. Local toolchains: v4.30.0, v4.32.0, v4.32.2, v4.34.0 and v4.35.0 are installed.

## Appendix C. Audit corrections applied

The audit is `.audit` in [research/technique-survey.json](research/equivalents-survey/technique-survey.json). Card ids are those of this file.

1. The light-cone results were confirmed and extended to L = 16 (count 316, two MFWs; 32 s rather than the projected 80 s) → D2, Appendix B.8.
2. The draft's first shortlist item was aimed along the wrong axis; exact realizability replaces it, and its kill rule was wrong → Summary, D2, D12, S1, S9.
3. The recommended Stephan files import axioms; only the Ceiling-Orbits Stanley files and the clean ForMathlib files are axiom-free → A1 (table), A2, A5, B3, S2, 4.3.
4. A Lean Morse–Hedlund exists outside our library (Stephan's `InfiniteComplexity.lean`) → B4, C8.
5. Duhamel–Cartier needs the rule-54 and F-FIN controls and is rated low → B1, B5, S4, 4.1.
6. Barrier scope: B1 and B6 are Q01-only; the c7 lasso for CQ01 and any Absorption barrier are unproved → 0.5, 1.2, C6, D6, D7, D9, F3, F8, S5, S7, 4.1.
7. Condrey's H(2, w) ≥ w is a sketch, and the sharp horizons are not formalised → D1, D10, S6, 4.1.
8. First Proof batches 1 and 3 were conflated; ProofCouncil is not independent of GPT-6 Astra; two GPT-6 Astra figures are unverified → 1.4, E5, E8.
9. Aletheia: 4 novel and 9 literature answers out of 13 (not 4 and 8); "none at paper level" is contestable → 1.4, E5.
10. #1051's golden-ratio threshold came from human-AI interaction; #258's model credit and date → A3.
11. Subspace-Theorems is Apache-2.0 and reports Roth landed; the NKR refutation is in Transcendence-Criteria; licence list → 0.6, A9.
12. Sun's Catalan claim is arXiv 2609.04176; arXiv 2609.22339 is Wachs's critique → 1.4, A9.
13. OpenAI's ten proofs have been audited (Sienicki & Sienicki); toolchain v4.32.0 → 1.4, E6, E9.
14. arXiv 2305.01375 is Diddy, and arXiv 2409.10124 is "Ants on the highway" → D11.
15. Gravner–Griffeath's priority for unbounded diagonal periods; Ikram's priority for the strip method → B2, C1, F12, 1.3.
16. p_c(20) ≥ 2^20 − 96 only; A214560 is a digit-growth conjecture and the "every model failed" claim is unverified; A267581 confirmed → 1.4, E4, F15.
17. Kernel bugs: #14484's model is unverified; release dates; replay under v4.35.0; third-party pre-fix toolchains; PBLean and lrat-catcher run natively → 1.4, E6, D10, D12, S1.
18. placego halted twice; SW-01 details (2 wounded, 3 rule-30 proposals); #90's Lean is third-party and arXiv 2605.20695 is a human expository note; the empty-hexagon formalisation found only a small error → 1.1, E3, E8, D10.

Added techniques: D12 (exact realizability), D13 (learned rankings), D14 (spin models), D15 (solvability tests), C10 (maximum-order and expansion complexity), E10 (PatternBoost), E11 (Equational Theories Project).

Smaller fixes made in this revision beyond the audit: rule 167 acts as the affine rule 165 on its single-seed orbit rather than being affine itself (E4); the 34 maximal-degree rules have degree 2t + 1, not rule 30's 2t − 1 (F15); the verifier's refuted claim concerned words in the first 10⁷ bits (F16, S8).


Fixes made by the final check:
- D2 and S9: the claim that the L = 16 MFWs change no filtered maximum now names the widths the audit checked (W = 56, 96, 128).
- D2: 0.33 bits is 2.7 times the 0.122 ceiling and over four times the measured 0.07–0.08.
- 0.6: "the audit checked these against GitHub" now reads "most of these".
- E11: the formal-verification label now reads "Formal (3rd party; every case checked in Lean), not rebuilt".
- E9: the Navier–Stokes and CDC claims now carry the survey's sources and their contested status.
- A9: openai/math's Catalan and mu(pi) = 2 results and Liu–Jiang–Zhang's mu(log r) = 2 now read as claims; the latter discloses no AI use.
- Summary: AI's verified results are described as short arguments "on related problems".
- E2: B7 is labelled "(derived, D8)".
- 4.1: rule 54 has the same structure as rule 30, and c7 the same recursion; rule 54's source term differs.
- D12 and D10: lrat-catcher is treated at the bv_decide/ofReduceBool trust level.
- S1: the continue/kill rule was rewritten (S1 above), the Jacobian-conjecture item now reads as a claim, and the batch-3 citation notes that its URL was not recorded.