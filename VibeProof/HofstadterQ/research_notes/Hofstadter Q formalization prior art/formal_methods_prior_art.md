# Formal / machine-checked prior art on Hofstadter's Q-sequence and its relatives (as of 2026-10-10)

*Tags: **[V]** means I opened the primary artifact (file, commit, PR or issue thread, arXiv or Zenodo record) this session. **[S]** means secondhand (a search-engine summary, a third party's description, or a claim the artifact makes about unpublished work). All GitHub searches used the authenticated `gh` CLI on 2026-10-10. GitHub code search does not index some archived or large repositories (see §10), so a "0 hits" result there is weak evidence.*

## 1. Has anyone formalized any part of "Q is total" or a close relative? (master inventory)

### Takeaway
No proof assistant has a proof, or even a published attempt at a proof, that Hofstadter's Q is total. The closest artifacts are four:
- A relational predicate `IsHofstadterQ` in google-deepmind/formal-conjectures, in place since 2026-09-12.
- An LLM-generated audit, published 2026-09, with a sorry-free Lean proof that every `IsHofstadterQ` solution is never eventually constant. It also claims (unpublished) Lean proofs of uniqueness and of `f n ≤ n`, and proposes a `well_defined : answer(sorry) ↔ ∃ f, IsHofstadterQ f` statement.
- Open issue #6544, which shows that the repository's `eventually_const` statement is already equivalent to "the Q-recursion dies".
- Benchmark tasks that wrap Q-like specs.

Among the relatives, only Hofstadter G/H and the generalized F_k have deep formal developments (Letouzey's Coq/Rocq project, 2015–2026), and totality is trivial there. The parity-perturbed Q has only a plain-Python certificate. Conway's sequence has only a definitional predicate (Meta's atlas-lean, 2026-10-05). V, Tanny, Conolly, Golomb's and Ruskey's initial conditions, and Fox's slow relatives have no formal artifacts that I could find.

### Cited Findings
Inventory (one row per artifact):

| # | Artifact (system) | Date(s) | What is defined / proven | How partiality is handled | Source |
|---|---|---|---|---|---|
| 1 | formal-conjectures `ErdosProblems/422.lean`, current (Lean 4 + Mathlib) | predicate since 2026-09-12 (PR #5791); file created 2025-11-11 | `IsHofstadterQ (f : ℕ+ → ℕ+)`. Tests `f 3 = 2` and `f 4 = 3` are proved. Four `sorry` research statements, each of the form `∀ f, IsHofstadterQ f → …` | Relational predicate with side conditions `f (n-1) < n ∧ f (n-2) < n`. Existence is not asserted. **[V]** | [422.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/422.lean), [PR #5791](https://github.com/google-deepmind/formal-conjectures/pull/5791) |
| 2 | Same file, original version | 2025-11-11 → 2026-09-12 | `partial def f : ℕ+ → ℕ+` with the same four questions | Opaque constant with no equation lemmas, so the statements never referred to Q. **[V]** | [commit 6708d75f09](https://github.com/google-deepmind/formal-conjectures/commit/6708d75f09), [issue #5649](https://github.com/google-deepmind/formal-conjectures/issues/5649) |
| 3 | LLM audit of 422 (tadamcz/fc-review-results, audit of FC commit aea251bb26; run 2026-09-23) | 2026-09 | Published sorry-free Lean: `erdos422_not_eventuallyConst`, and `eventually_const` RHS ↔ `¬∃ f, IsHofstadterQ f`. Claimed but unpublished: uniqueness, `IsHofstadterQ f → f n ≤ n`, `growth_rate` provable with answer `n`, and Q(n) ≤ n for n ≤ 200,000. Proposes `erdos_422.variants.well_defined` | Works with the FC predicate. **[V]** for the published code and text; **[S]** for the unpublished scratch proofs | [audit JSON](https://github.com/tadamcz/fc-review-results/blob/main/data/aea251bb26/files/ErdosProblems/422.json), [issue #6544](https://github.com/google-deepmind/formal-conjectures/issues/6544) |
| 4 | vericoding / FVAPPS task 2638 (Lean 4) | FVAPPS paper 2025-02-08; vericoding files 2025-09-16/26 | `def hofstadter_Q : Nat → Nat \| 0 => 0 \| n => sorry` with `sorry` theorems: positivity, first terms, recurrence for n ≥ 3 (truncated `-`), and a trivial determinism lemma | Pads with Q(0)=0 and truncated subtraction. Satisfiability is implied by totality (inference, §2). **[V]** | [LF2638_specs.lean](https://github.com/Beneficial-AI-Foundation/vericoding-benchmark/blob/main/specs/LF2638_specs.lean), [fvapps_002638.lean](https://github.com/Beneficial-AI-Foundation/vericoding/blob/main/benchmarks/lean/fvapps/files/fvapps_002638.lean) |
| 5 | facebookresearch/atlas-lean `ConwayHofstadterLikeSequence.lean` (Lean 4) | 2026-10-05 | `IsConwayHofstadterLikeSequence k c` (Pelesko's k-generalization of Conway's $10,000 sequence). Tests only | Prop predicate. Pelesko's residue convention keeps indices in [1, n−1]. **[V]** | [file](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ConwayHofstadterLikeSequence.lean) |
| 6 | provables/sequencelib A005206 (G), A005378 (Female) (Lean 4) | 2025-10 to 2025-12 | Synthesized closed-loop programs (Gauthier–Urban QSynt) with value checks to index 100 | Not nested recursion. Total by construction. **[V]** | [A005206.lean](https://github.com/provables/sequencelib/blob/main/Sequencelib/Synthetic/A005/A005206.lean) |
| 7 | letouzey/hofstadter_g (Coq/Rocq) | 2015-08-27 → 2026-10-09 | G, H and the F_k family: existence, uniqueness, Fibonacci-like numeration, morphic words, frequencies, discrepancy, pointwise order | Inductive graph relation plus a custom induction principle; `Program Fixpoint` with subset types; fuel `recf`. **[V]** | [repo](https://github.com/letouzey/hofstadter_g) |
| 8 | bloomberg/crane test `hofstadter_q_fuel` (Rocq) | file moved 2026-03-22 | Fuel-bounded Q (fuel n·n+1, returns 1 when fuel runs out, Q(0)=0) used as an extraction regression test. No theorems | Fuel plus junk values. **[V]** | [LoopifyMultiRecursion.v](https://github.com/bloomberg/crane/blob/main/tests/regression/loopify_multi_recursion/LoopifyMultiRecursion.v) |
| 9 | Why3 gallery `mutual_recursion.mlw` | 2020-05-01 | Termination of Hofstadter Female/Male, with postconditions `1 ≤ f n ≤ n` and `0 ≤ m n < n` | Variants plus bound postconditions. **[V]** | [file](https://github.com/AdaCore/why3/blob/master/examples/mutual_recursion.mlw) |
| 10 | Mantovanelli Zenodo certificate (parity-perturbed Q) | v3.0.0, 2026-07-22 | Python audit (`run_all_checks.py`, 9 checks) | "not a Lean, Coq, Isabelle, or HOL formalization". **[V]** | [Zenodo 10.5281/zenodo.21495335](https://doi.org/10.5281/zenodo.21495335) |

- Benchmarks and harnesses that only *wrap* the 422 statements, with no results:
  - AlphaProof Nexus attempted `erdos_422`, `.variants.surjective` and `.variants.eventually_const`. Its results repository "contains only problems where successful proofs were discovered", and its tree has no 422 file. **[V]** [attempted list](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/erdos_problems_attempted.txt), [README](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/README.md)
  - FormalConjectures-Bench, 2026-05: paired prove/refute tasks on the `partial def` version, pinned to FC commit 233a10e857 and Lean v4.27.0, with `oracle_status = "none"`. **[V]** [task](https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/main/tasks-v2/erdosproblems-422-eventually-const-refute)
  - Aristotle (Harmonic) submission inputs, 2026-01-04: the `partial def` version, labelled "AVOID"/"untouched". **[V]** [submission](https://github.com/kavanaghpatrick/aristotle-math-problems/blob/main/submissions/erdos/tier5/erdos_422_erdos_422.lean), [closure CSV](https://github.com/kavanaghpatrick/aristotle-math-problems/blob/main/analysis/erdos_closure_labeled.csv)
  - lean-genius proof-target list: 422 is listed as "research", with no proof. **[V]** [proof-targets.json](https://github.com/rjwalters/lean-genius/blob/main/scripts/erdos/data/proof-targets.json)
- The erdosproblems database records 422 as `status: open` (2025-08-31), `oeis: ["A005185"]`, `formalized: yes` (2025-11-11) and `formal_status: unformalized`. **[V]** [problems.yaml](https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml)
- Searches for relatives:
  - Global GitHub code search for `A004001`, `A063882` and `A046699`: no formal (Lean, Coq, Isabelle, Agda) hits.
  - "Tanny sequence" and "Conolly": only bibliographic or OEIS-scrape hits.
  - formal-conjectures (main `OEIS/`, 229 files, and the `auto_oeis` branch, 1,516 paths) and sequencelib (26,336 paths): none of the IDs A005185, A004001, A063882, A046699, A006949, A005374, A005229, A055748, A244477 or A188670. sequencelib does have A005206 (G) and A005378 (Female) (row 6). **[V]** [FC OEIS folder](https://github.com/google-deepmind/formal-conjectures/tree/main/FormalConjectures/OEIS), [auto_oeis mapping](https://github.com/google-deepmind/formal-conjectures/blob/auto_oeis/FormalConjectures/OEIS/Auto/THEOREM_MAPPING.txt), [sequencelib](https://github.com/provables/sequencelib)

### Inferences
- What exists for Q is: the relational definition; tiny unfolding tests (f 3, f 4); and, from the audit, trivial structural lemmas (uniqueness, `f n ≤ n` under the predicate, no eventual constancy). Nothing touches the inductive heart of totality, and no verified computation of Q values has been published.
- A new Lean project would duplicate nothing substantive. It could upstream three things to formal-conjectures: the uniqueness lemma, the `¬ EventuallyConst` lemma, and a direct `well_defined` statement. That fix is pending: issue #6544 is still open.
- The parity-perturbed Q is a clear "first formalization" opportunity. Two human or computer-assisted proofs exist (Mantovanelli; Cloitre), and neither is machine-checked.

### Gaps
- The audit's uniqueness proof (`scratch5.lean`/`scratch6.lean`) and its Q(n) ≤ n computation (`scratch4.lean`) are described but not published. Their method (`#eval`, `native_decide` or kernel) is unknown.
- I did not search for Golomb's or Ruskey's initial-condition variants by OEIS ID in global code search; I grepped them only in the formal-conjectures and sequencelib trees.

## 2. Lean 4 / Mathlib / other Lean projects, and everything in google-deepmind/formal-conjectures

### Takeaway
Mathlib has nothing on Q or meta-Fibonacci sequences. Its only Hofstadter-related file is the GEB MIU system.

In formal-conjectures, 422.lean was a `partial def` for ten months and has been a predicate since 2026-09-12. The well-definedness question was explicitly discussed in 2025 and left out. Today the `eventually_const` variant is provably equivalent to "Q dies", per open issue #6544.

Other Lean artifacts are one-off: the FVAPPS/vericoding spec, the atlas-lean Conway-like predicate, and sequencelib's synthesized G and Female. None proves anything beyond small tests.

### Cited Findings
**Mathlib.** The only "Hofstadter" files in Lean that GitHub code search finds:
- Mathlib `Archive/MiuLanguage/Basic.lean` (the MIU formal system from GEB) and its copies.
- formal-conjectures 422 and 423.
- atlas-lean.
- Two vericoding files.

`HofstadterQ` (any language) hits only programming exercises and formal-conjectures. `meta-Fibonacci` and `metaFibonacci` in Lean return 0 hits. **[V]** [MIU file](https://github.com/leanprover-community/mathlib4/blob/master/Archive/MiuLanguage/Basic.lean)

Issue and PR search on `leanprover-community/mathlib4` for "Hofstadter", "nested recursion" and "McCarthy" returns 0 relevant results. **[V]** [mathlib4](https://github.com/leanprover-community/mathlib4)

**formal-conjectures 422, history and discussion:**
- Issue #721 (mo271, 2025-10-05, closed 2025-12-11) requested problem 422. **[V]** [#721](https://github.com/google-deepmind/formal-conjectures/issues/721)
- PR #692 (Anirudh Rao, opened 2025-09-28, merged 2025-11-11, co-author Paul Lezeau) added `partial def f : ℕ+ → ℕ+` and the four statements. **[V]** [PR #692](https://github.com/google-deepmind/formal-conjectures/pull/692)
  - In review, Paul Lezeau proposed asking "whether the sequence `f` must eventually terminate".
  - Salvatore Mercuri (2025-10-02) answered that the other reading of termination, "whether one reaches a point at which `f n` cannot be defined", is "already captured in the definition". The stationarity variant `eventually_const` was added instead. So well-definedness was considered and not stated.
- Commit a22f98abef (Moritz Firsching, 2026-01-06) reordered the statements to `answer(sorry) ↔ …`. **[V]** [422 history](https://github.com/google-deepmind/formal-conjectures/commits/main/FormalConjectures/ErdosProblems/422.lean)
- PR #2917 (2026-03-03) was closed unmerged about an hour later. It was a "loophole" PR, stated to be generated by "Claude Sonnet 4.6 in OpenCode", adding `erdos_422.variants.known_result : f 1 = 1 ∧ f 2 = 1 := by sorry` tagged "formally solved". It is not a result. **[V]** [PR #2917](https://github.com/google-deepmind/formal-conjectures/pull/2917)
- Issue #4923 (2026-08-13, open) notes that `growth_rate` is self-answering: use the target function as the Big-O answer, then `isBigO_refl` closes it. **[V]** [#4923](https://github.com/google-deepmind/formal-conjectures/issues/4923)
- Issue #5649 (tadamcz, 2026-09-11, an LLM audit "not reviewed by a human") reported that the `partial def` is "an opaque constant … with no equation lemmas". **[V]** [#5649](https://github.com/google-deepmind/formal-conjectures/issues/5649)
- PR #5791 (Salvatore Mercuri, opened 2026-09-11, merged 2026-09-12, approved by mo271) fixed this. **[V]** [PR #5791](https://github.com/google-deepmind/formal-conjectures/pull/5791)
  - It replaced the `partial def` with `IsHofstadterQ`, added tests f3 and f4, and cited A005185.
  - Its description says: "at most one function satisfies the predicate, and one does exactly when the sequence is well-defined for all n". No proof of this was added.
- Commit 6fbb54f24c (2026-09-18) "modulized" the file. **[V]** [422 history](https://github.com/google-deepmind/formal-conjectures/commits/main/FormalConjectures/ErdosProblems/422.lean)
- Issue #6544 (tadamcz, 2026-09-24, **open**) argues that any `IsHofstadterQ` solution is never eventually constant, so `eventually_const`'s RHS is equivalent to `¬ ∃ f, IsHofstadterQ f`. The argument: if f(n) = c for all large n, then at n = N + c + 2 the recurrence gives c = 2c. **[V]** [#6544](https://github.com/google-deepmind/formal-conjectures/issues/6544)

**The audit behind #6544** (tadamcz/fc-review-results, "Automated audit of google-deepmind/formal-conjectures", repo created 2026-09-08). The 422 record has run name `fc-review-opus55`, cost $8.54 and 56.5 working minutes; its transcript is in an S3 bucket named `epochai-public-eval-logs-manual`. **[V]** [audit JSON](https://github.com/tadamcz/fc-review-results/blob/main/data/aea251bb26/files/ErdosProblems/422.json)
- It publishes a sorry-free Lean file containing:
  - `theorem erdos422_not_eventuallyConst {f} (hf : Erdos422.IsHofstadterQ f) : ¬ EventuallyConst f atTop`.
  - An `example` showing `type_of% @Erdos422.erdos_422.variants.eventually_const ↔ ¬ ∃ f, IsHofstadterQ f`.
  - It reports "propext, Classical.choice, Quot.sound" as the only axioms.
- Its notes claim Lean checks, unpublished and run in its workspace, of four facts:
  - `IsHofstadterQ` has at most one solution.
  - `∀ f, IsHofstadterQ f → P f` ↔ `(¬∃ f, IsHofstadterQ f) ∨ ∃ f, IsHofstadterQ f ∧ P f`.
  - `IsHofstadterQ f → f n ≤ n`, so `growth_rate` is provable with the answer `fun n ↦ (n:ℝ)`.
  - Q(n) ≤ n for n ≤ 200,000 by computation.
- Its suggested fixes are:
  - `theorem erdos_422.variants.well_defined : answer(sorry) ↔ ∃ f : ℕ+ → ℕ+, IsHofstadterQ f`.
  - `eventually_const` restated as `answer(False) ↔ ∃ f, IsHofstadterQ f ∧ EventuallyConst f atTop` (category textbook).
  - `surjective` restated as `∃ f, IsHofstadterQ f ∧ f.Surjective`, because the ∀-form has the wrong polarity if Q dies.
- These fixes are not merged. Issue/PR search on the repo for "422", "Hofstadter" and "Q-sequence" shows no PR after #5791 touching 422. **[V]** [issue search](https://github.com/google-deepmind/formal-conjectures/issues?q=422)

**Other files in formal-conjectures:**
- In-repo code search: "Hofstadter" hits only 422 and 423; "A005185" only 422; "A004001", "A063882", "A046699" and "meta-Fibonacci" return 0; "Golomb" hits 365, 366 and 508 (unrelated); "Conway" hits `Wikipedia/Conway99Graph.lean` and 391 (unrelated). **[V]** [repo](https://github.com/google-deepmind/formal-conjectures)
- `ErdosProblems/423.lean` is a different "Hofstadter sequence", A005243 (consecutive sums). **[V]** [423.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/423.lean)
  - It uses the same relational style (`IsHofstadterSeq`), has proven tests a3 and a4, and cites "[Ta26] Tang, Q., The Hofstadter consecutive-sum sequence omits infinitely many positive…".
  - PR #6055 (2026-09-18) proved a test lemma `unbounded_iff_infinite_complement`.

**vericoding / FVAPPS:**
- FVAPPS (Dougherty & Mehta, arXiv 2502.05714, 2025-02-08) turns APPS unit tests into `sorry`'d Lean 4 theorems: 4,715 samples, 1,083 curated. **[V]** [FVAPPS](https://arxiv.org/abs/2502.05714)
- Sample 2638 is the Hofstadter Q spec in row 4 of §1. It appears in `Beneficial-AI-Foundation/vericoding` (path renamed 2025-09-16) and in `vericoding-benchmark` (`LF2638_specs.lean`, added 2025-09-26 by Shaowei Lin). **[V]** [LF2638](https://github.com/Beneficial-AI-Foundation/vericoding-benchmark/blob/main/specs/LF2638_specs.lean)

**atlas-lean** ("ATLAS Autoformalized Textbook Library At Scale", Meta, repo created 2026-05-26). **[V]** [file](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ConwayHofstadterLikeSequence.lean), [test](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ConwayHofstadterLikeSequence.lean)
- Commit c5bbed128f (Adam Kiezun, 2026-10-05, "Import NumberTheory 05: NumberTheory, Recurrences") added `conwayHofstadterResidue` and the predicate `IsConwayHofstadterLikeSequence (k) (c : ℕ → ℕ)`, following Pelesko, *Generalizing the Conway–Hofstadter $10,000 Sequence* (JIS vol. 7).
- The test file proves two `conwayHofstadterResidue` examples by `decide` and `IsConwayHofstadterLikeSequence 2 c → c 3 = 2`. No other theorems exist, and there are no other meta-Fibonacci files in that repo's tree.

**sequencelib** (Moreira & Stubbs; "more than 25,000 sequences" and "more than 1.6 million theorems about their values"; arXiv 2601.11757, 2026-01-16). **[V]** [paper](https://arxiv.org/abs/2601.11757), [A005206](https://github.com/provables/sequencelib/blob/main/Sequencelib/Synthetic/A005/A005206.lean)
- Its Hofstadter-family entries are QSynt programs (Gauthier & Urban, AAAI-23) transpiled from SML, e.g. `A005206 x := Int.toNat <| (loop (λ x y ↦ y*y/(2+x) + y) (1+x) 0 - 1) - x` with `@[OEIS := A005206, offset := 0, maxIndex := 100, derive := true]`.
- These are closed iterative formulas, not the nested recursion.

### Inferences
- **FVAPPS spec.** `Q 0 = 0` is fixed, and positivity forces `Q(n−1) ≥ 1`. So the spec pins down a unique "0-padded" Q, and it is satisfiable iff that padded recursion never returns 0 at n ≥ 1. Totality of the true Q implies this, but not conversely. A sorry-free solution would therefore settle a statement at least close in difficulty to the open problem. This is an example of an autoformalized benchmark task that hides an open problem.
- **atlas-lean.** With k = 1, Pelesko's family reduces to Conway's a(n) = a(a(n−1)) + a(n−a(n−1)): the residue of a(n−1) mod n−1 is a(n−1) when 1 ≤ a(n−1) ≤ n−1, and it is mapped to n−1 when it would be 0. Because both lookbacks always lie in [1, n−1], existence is trivial for every k. It is not proved in the file, though.
- **AlphaProof Nexus.** Its attempts must have used the opaque `partial def` version. The repo was created 2026-05-13 and last pushed 2026-07-21, before the 2026-09-12 fix. Under that version no non-trivial statement about f was provable either way.

### Gaps
- I could not view the AlphaProof Nexus paper's per-problem logs, so I don't know how long it ran on 422.
- I did not check closed-unmerged branches or forks of formal-conjectures beyond the issue/PR search.

## 3. Coq/Rocq: Letouzey's Hofstadter G/H/F_k development and other developments

### Takeaway
Letouzey's `hofstadter_g` (2015–2026, active this week) is the largest formal development on any Hofstadter nested recurrence. It covers G, H and the family f_k(n) = n − f_k^{(k)}(n−1). It neither mentions nor touches Q or Conway's sequence.

Its definitional techniques transfer directly to Q: an inductive graph relation with a custom induction principle using the bound G n a → a ≤ n, `Program Fixpoint` with subset types, a fuel parameter, and FlexArray tabulation with a correctness lemma. The only other Coq artifact naming Q is a fuel-based extraction test in Bloomberg's Crane.

### Cited Findings
Repository facts: created 2015-08-27; last push 2026-10-09 ("almost compat with 9.2"); depends on Coq ≥ 8.16 and ≤ 9.1 plus Coquelicot; public domain. **[V]** [repo/README](https://github.com/letouzey/hofstadter_g)

The README lists the documentation **[V]** [README](https://github.com/letouzey/hofstadter_g):
- Letouzey, Li, Steiner, "Pointwise order of generalized Hofstadter functions G, H and beyond", J. Integer Sequences 29 (2026). [JIS](https://cs.uwaterloo.ca/journals/JIS/VOL29/Letouzey/letouzey3.html), [HAL hal-04715451](https://hal.science/hal-04715451)
- Letouzey, "Generalized Hofstadter functions G, H and beyond: numeration systems and discrepancy", preprint 2025. [HAL hal-04948022](https://hal.science/hal-04948022)
- Technical report "Hofstadter's problem for curious readers" (2015). [HAL hal-01195587](https://hal.science/hal-01195587)
- Talks: PPS'18, Formath'23, FSMP'23, PPS'24, OWCW 2025-03-11.

The README describes the file contents **[V]** [README](https://github.com/letouzey/hofstadter_g):
- `FunG.v`, `GenG.v`, `Fast.v`, `GenFlip.v`, `GenAdd.v`, `Shift.v`, `DirectGrowth.v` (f_k ≤ f_{k+1}).
- Words, frequencies and discrepancy: `F3.v`, H at distance < 1 of n·τ_3; `F4.v`; `F5.v`, unbounded.
- `Siegel.v` ("the least Pisot number is the Plastic Ratio"), `RootEquiv.v`, `Equidistrib.v`.

How the nested recursion is handled **[V]**:
- [FunG.v](https://github.com/letouzey/hofstadter_g/blob/main/FunG.v):
  - `Inductive G : nat -> nat -> Prop` with constructors `G0 : G 0 0` and `GS n a b c : G n a -> G a b -> S n = c+b -> G (S n) c`.
  - `G_le : G n a -> a <= n` ("used for proving that G is a total function").
  - A custom induction principle `G_rec`, functionality `G_fun`, and existence `g_spec n : {a | G n a}`, defined via `G_rec`, with `g n := proj1_sig`.
- [FunG_prog.v](https://github.com/letouzey/hofstadter_g/blob/main/FunG_prog.v): `Program Fixpoint g_spec n {measure n} : {r : nat | G n r} := … S n - g_spec (g_spec n)`. The obligations use `G_le`, and a lemma shows it equals `FunG.g`.
- [GenG.v](https://github.com/letouzey/hofstadter_g/blob/main/GenG.v): "One possible trick to define [f] via Coq structural recursion is to add an extra parameter [p]" (`recf k p n`, f k n := recf k n n), with `f_recf` (fuel independence for n ≤ p) and `f_eqn`.
- Letouzey's 2023 talk slides (in French) summarize the choices: "Décroissance non structurelle : pas de Fixpoint", "Spécification via un prédicat inductif", "Program Fixpoint (mais lourd)", "Plus rapide : fopt fonctionnant par table". [talks/2](https://github.com/letouzey/hofstadter_g/blob/main/talks/2/expose.md)
- [Fast.v](https://github.com/letouzey/hofstadter_g/blob/main/Fast.v): binary `N` plus a persistent `FlexArray` ("log access time") tabulation, with `Lemma f_spec` and `A_spec` proving that the fast versions equal the spec functions.

Code search for "Conway" and "Q-sequence" in that repo returns 0 hits. A grep of FunG.v, GenG.v, Fast.v and the talk sources finds no Q or Conway mention. **[V]** [repo](https://github.com/letouzey/hofstadter_g)

Bloomberg Crane ("extraction system from Rocq to … C++", repo created 2025-11-22) has `Fixpoint hofstadter_q_fuel (fuel n : nat)` with `hofstadter_q n := hofstadter_q_fuel (n*n+1) n`, used only as a "multi-way recursion" extraction regression test. **[V]** [file](https://github.com/bloomberg/crane/blob/main/tests/regression/loopify_multi_recursion/LoopifyMultiRecursion.v)

General Coq/type-theory methodology for nested partial recursion:
- Bove & Capretta, "Nested General Recursion and Partiality in Type Theory" (TPHOLs 2001, LNCS 2152, 121–135): inductive domain predicates defined simultaneously with the function, using inductive-recursive definitions. **[S]** [Chalmers record](https://research.chalmers.se/en/publication/47408)
- Larchey-Wendling & Monin's "Braga method": Coq programs "without a priori knowledge on their termination domain", 2021 chapter; TYPES 2018 paper on simulating induction-recursion using Paulson's normalization. **[S]** [lc2021.pdf](https://members.loria.fr/DLarchey/files/papers/lc2021.pdf), [TYPES18](https://www-verimag.imag.fr/~monin/Publis/Docs/types18-indrec.pdf)
- The same authors' ITP 2023 proof pearl on µ-recursive algorithms. **[S]** [ITP 2023](https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.21/LIPIcs.ITP.2023.21.pdf)

### Inferences
- For Q, Letouzey's relational pattern carries over, but with a crucial difference. For G, the bound `G_le` (a ≤ n) is provable by simple induction, which makes totality easy. For Q, the analogous bound Q(m) ≤ m is exactly the open problem. A Coq or Lean development of Q therefore splits into an easy part (graph relation, uniqueness, prefix existence up to the first failure) and an open part (an unbounded Q(m) ≤ m).
- Letouzey's Fast.v (FlexArray plus a correctness lemma) is the closest precedent for verified tabulated computation of a nested recurrence inside a proof assistant.

### Gaps
- I did not open every `.v` file, e.g. `Article1.v`, `Article2.v` and `Words.v`, for incidental Q or Conway mentions. Code search returned none.
- I did not locate coq-community or opam packages on nested recurrences. An opam search was not run.

## 4. Isabelle/AFP: Hofstadter entries? Function-package treatment of nested and partial recursion

### Takeaway
The AFP has no entry on Hofstadter sequences, Conway's sequence or meta-Fibonacci recurrences. The Isabelle documentation and examples use McCarthy 91 and a "nested zero" function, not Q, to illustrate nested recursion whose termination needs facts about the function itself. The relevant machinery is Krauss's function package: the `_dom` predicate, `psimps`, `pinduct` and `(domintros)`.

### Cited Findings
- The AFP mirror's `thys/` directory has 1,041 entries (mirror pushed 2026-10-08). A name grep for hofstadter, conway, golomb, fibonacci, recurr, nested, mccarthy and sequence finds only unrelated entries: `Conway_Circle`, `Farey_Sequences`, `Linear_Recurrences`, `Lucas_Theorem`, `Nested_Multisets_Ordinals`, `Partial_Function_MR`, `Sturm_Sequences`, etc. **[V]** [mirror-afp-devel](https://github.com/isabelle-prover/mirror-afp-devel)
- Code search for "Hofstadter" in the AFP mirror and in the Isabelle repository mirror returns 0 hits. The isa-afp.org search page is JavaScript-only and could not be queried. **[V]** [mirror-isabelle](https://github.com/isabelle-prover/mirror-isabelle)
- `src/HOL/Examples/Functions.thy`, "Nested recursion" section **[V]** [Functions.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Examples/Functions.thy):
  - `function nz` with `nz (Suc x) = nz (nz x)`. The lemma `nz_is_zero` is proven under `nz_dom x` and then used for `termination nz`.
  - McCarthy's `f91 n = (if 100 < n then n - 10 else f91 (f91 (n + 11)))`, with `f91_estimate` proven under `f91_dom n`.
  - No "Hofstadter" string.
- Krauss's tutorial `src/Doc/Functions/Functions.thy` explains partial functions via `findzero`. It covers `findzero_dom`, `findzero.psimps` and `findzero.pinduct`, plus requesting introduction rules with `function (domintros)`. It cites `krauss_phd` for details and contains no "Hofstadter" string. **[V]** [Doc/Functions](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Doc/Functions/Functions.thy)
- AFP `Nested_Multisets_Ordinals/McCarthy_91.thy` (Jasmin Blanchette, 2017): "Termination of McCarthy's 91 function". A tail-recursive implementation `g` is proved terminating with the multiset order (Dershowitz–Manna). **[V]** [McCarthy_91.thy](https://github.com/isabelle-prover/mirror-afp-devel/blob/master/thys/Nested_Multisets_Ordinals/McCarthy_91.thy)

### Inferences
- In Isabelle, Q could be stated as `function (domintros) Q` with totality expressed as `∀n ≥ 1. Q_dom n`, though failure at index ≤ 0 needs an explicit encoding, e.g. an option result. I found no source that uses Q as the canonical "unknown totality" example; the Isabelle literature uses McCarthy 91 and `findzero`.

### Gaps
- I did not read Krauss's PhD thesis or the `partial_function` paper. Whether they mention Hofstadter is unverified.
- The `Partial_Function_MR` entry was identified by name only.

## 5. Lean-specific mechanisms for possibly-partial nested recursion (`partial def`, `partial_fixpoint`, WF recursion), and whether Lean docs or talks use Q

### Takeaway
`partial def` is unusable for reasoning: it is an opaque constant, which is precisely what broke formal-conjectures 422 for ten months. `partial_fixpoint` (Lean ≥ v4.17.0, 2025-03) accepts nested recursion only in a monad such as `Option`, with `none` standing for non-termination. The canonical worked example of proving totality afterwards is McCarthy 91 (Breitner, Zulip, 2025-02-20; also in Lean's test suite). No Lean doc, test or talk I found uses Hofstadter Q.

### Cited Findings
- `partial def` "elaborates … as an opaque constant `ℕ+ → ℕ+` with no equation lemmas", per PR #5791's description, merged by the maintainers. **[V]** [PR #5791](https://github.com/google-deepmind/formal-conjectures/pull/5791)
- `partial_fixpoint` was introduced by lean4 PR #6355 (opened 2024-12-10), with follow-ups #6477 ("theory", 2024-12-30) and #6506 ("monotonicity tactic", 2025-01-02). It shipped in v4.17.0, published 2025-03-03. **[V]** [PR #6355](https://github.com/leanprover/lean4/pull/6355), [v4.17.0 release](https://github.com/leanprover/lean4/releases/tag/v4.17.0)
- Lean reference manual §7.6.4 "Partial Fixpoint Recursion" **[V]** [manual page](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/):
  - The return type must be inhabited and all recursive calls in tail position, unless the return type is a monad with a `Lean.Order.MonoBind` instance "such as `Option`". In that case calls may occur under `bind`.
  - Examples: `find`, `loop`, `Array.find`, `List.findIndex` (with a monotonicity failure when pattern-matching on the result), and `Tree.rev`.
  - Nested Ackermann in `Option`: `| x + 1, y + 1 => do ack x (← ack (x + 1) y)`.
  - "In the Option monad, then partial fixpoint equals Option.none on all function inputs for which the defining equation specifies non-termination." A generated `.partial_correctness` theorem is shown for `List.findIndex`.
  - The construction is a Knaster–Tarski least fixed point over `Lean.Order.CCPO`.
  - A string search of the full page finds 0 hits for "Hofstadter", "McCarthy" and "Collatz".
- Zulip #lean4 thread "McCarthy 91 function using partial_fixpoint" (Joachim Breitner, 2025-02-20) **[V]** [archive JSON](https://github.com/leanprover-community/archive/blob/master/zulip_json/270676-lean4/McCarthy.2091.20function.20using.20partial_fixpoint.json)
  - Breitner explains that well-founded recursion with `termination_by 101 - n` is "doomed" without changing the signature, "because we'd have to prove something about the function we are defining". He then defines `def f91 (n : Nat) : Option Nat := if n > 100 then pure (n - 10) else f91 (n + 11) >>= f91` with `partial_fixpoint`.
  - He proves `f91_spec_low`/`f91_spec_high` (by recursion), then `f91_total : (f91 n).isSome`, then defines `f91! n := (f91 n).get (f91_total n)` and derives its original nested equation. He adds: "This 'totalization' construction could presumably be even automated".
  - Markus Himmel points to Lean by Example's subtype-returning helper `M (n) : {m // m ≥ n - 10}` with `termination_by 101 - n`. He notes `#check Mc91.M.induct` hits a heartbeat timeout.
- Lean core tests **[V]**:
  - `tests/elab/partial_fixpoint_f91.lean` contains the f91 definition, a `partial_correctness`-based partial spec, and total-correctness proofs (moved into `tests/elab` 2026-02-25, PR #12590). [file](https://github.com/leanprover/lean4/blob/master/tests/elab/partial_fixpoint_f91.lean)
  - `tests/elab/partial_fixpoint_f91b.lean` (Breitner, 2026-07-09, PR #14335) checks that a *non-monadic* nested `f91 (f91 (n + 11))` with `partial_fixpoint` gives the error "Could not prove 'f91' to be monotone in its recursive calls". [file](https://github.com/leanprover/lean4/blob/master/tests/elab/partial_fixpoint_f91b.lean)
  - Code search of `leanprover/lean4` for "hofstadter" returns 0 hits.
- The manual's well-founded recursion section discusses nested calls only via lexicographic measures (Ackermann), plus `List.attach`/`wfParam` context enrichment. It does not show termination arguments that need facts about inner results. **[V]** [manual page](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)

### Inferences
- Q differs from McCarthy 91 in one important way. With guards, Q's recursion is downward: each call is to n − Q(n−1) < n once Q(n−1) ≥ 1. So an `Option`-valued Q with explicit checks, e.g. `if h : 1 ≤ a ∧ a < n then … else none`, can be defined by ordinary WF recursion on n; `partial_fixpoint` is optional.
- Either way, the open statement becomes `∀ n ≥ 1, (Q n).isSome`, equivalently `∃ f, IsHofstadterQ f`. Breitner's totalization recipe (`isSome` lemma → `Option.get` → derived equation) is the closest Lean template. The coordinator's "padded total definition" is a third route.
- The hard part is the invariant Q(m) ≤ m, not termination.

### Gaps
- I did not find a Lean FRO blog post or conference talk on `partial_fixpoint` beyond the manual, the release notes and the Zulip thread. A dedicated search was not run.

## 6. Walnut and automata methods: which Hofstadter-like sequences have machine-decided properties? Anyone on Q or the perturbed variant?

### Takeaway
Walnut, the decision procedure for automatic sequences, has been used on Fibonacci-synchronized relatives: Hofstadter's G and the "married" Female/Male functions via Quet's sequence, and Fibonacci-related sequences generally. A 2-automaticity result for a Hofstadter Q-variant (V-sequence lineage, Allouche–Shallit 2011) predates Walnut and gives an explicit automaton.

I found no application of Walnut to Q, Conway's sequence or the parity-perturbed Q. Mantovanelli's "finite-state" proof for the perturbed Q is a bespoke Python-checked certificate, not Walnut.

### Cited Findings
- Allouche & Shallit, "A variant of Hofstadter's sequence and finite automata", arXiv 1103.1133 (v1 2011-03-06, v2 2011-06-13). It analyzes "a variant of Hofstadter's Q-sequence", following Balamohan–Kuznetsov–Tanny, and shows it is 2-automatic. "An automaton computing the sequence is explicitly given." No software is named in the abstract. **[V]** [arXiv](https://arxiv.org/abs/1103.1133)
  - Published in J. Australian Math. Soc. **[S]** [Cambridge](https://resolve.cambridge.org/core/journals/journal-of-the-australian-mathematical-society/article/variant-of-hofstadters-sequence-and-finite-automata/3C01566E753B021FCF5689B3CD65644C)
- Shallit, "Proving properties of some greedily-defined integer recurrences via automata theory", arXiv 2308.06544 (2023-08-12). It uses "a decision procedure implemented in the free software Walnut" to prove a conjecture of Quet and link Quet's sequence to Hofstadter's "married" functions. **[V]** [arXiv](https://arxiv.org/abs/2308.06544)
- Dekking, "On Hofstadter's G-sequence", arXiv 2307.01471 (v1 2023-07-04, v3 2023-10-31). It characterizes G via the Wythoff sequences; the abstract mentions no Walnut or automata. **[V]** [arXiv](https://arxiv.org/abs/2307.01471)
- Campbell & Cloitre, "Meta-automatic Sequences", arXiv 2602.23395 (v1 2026-02-25, v2 2026-05-28). It combines meta-Fibonacci and automatic recurrences, with two "non-denestable" binary examples given explicit DFAO evaluations and 4-uniform morphisms. It references the Q recurrence and the Allouche–Shallit variant; the abstract does not mention Walnut. **[V]** [arXiv](https://arxiv.org/abs/2602.23395)
  - It also appears in JIS vol. 29 (2026), Art. 26.4.1. **[S]** [JIS](https://cs.uwaterloo.ca/journals/JIS/VOL29/Cloitre/cloitre20.html)
- Other Walnut work in this neighbourhood (not opened):
  - Cloitre & Shallit, "Some Fibonacci-Related Sequences", arXiv 2312.11706 (2023, Walnut). **[S]** [arXiv](https://arxiv.org/abs/2312.11706)
  - Shallit, "Proving Properties of φ-Representations with the Walnut Theorem-Prover", arXiv 2305.02672 (2023). **[S]** [arXiv](https://arxiv.org/abs/2305.02672)
  - "Frobenius Numbers and Automatic Sequences", arXiv 2103.10904: a search summary says its Theorem 13 treats a G-type sequence on lower Wythoff numbers as Fibonacci-synchronized, verified with Walnut. **[S]** [arXiv](https://arxiv.org/pdf/2103.10904)
- Mantovanelli's arXiv 2603.29622 is classified MSC 68Q45 (formal languages and automata) among others. The v3 comments say it replaces "the earlier finite-state closure argument" with an exact return-word induction and an explicit causality certificate. The v3 Zenodo certificate still contains a "122-rule transition kernel" over a "92-state domain". All checks run as a plain-Python audit (§8), not in Walnut or another automata tool. **[V]** [arXiv abs](https://arxiv.org/abs/2603.29622v3), [Zenodo](https://doi.org/10.5281/zenodo.21495335)

### Inferences
- Walnut needs the sequence, or a synchronized relation, to be automatic in some numeration system. Q is not known, or expected from its chaotic numerics, to be so. That likely explains why no one has tried Walnut on Q, but I found no source explicitly saying "Walnut fails on Q".
- The perturbed variant's binary-word reduction (odd values, "binary sequence with two backward cursor heads") is the kind of structure where automata methods might apply.

### Gaps
- I did not obtain the Walnut book's (Shallit 2022) index of Hofstadter-related examples, nor any Walnut treatment of V, Conolly or Tanny sequences. Searches for "Walnut" combined with "V-sequence", "Conolly" or "Tanny" returned nothing.

## 7. Termination-tool benchmarks (TPDB / termCOMP / AProVE): Hofstadter-style nested recursions?

### Takeaway
I found no Hofstadter-style entry in the Termination Problem Database. Conceptually, Q's open question is a value invariant / absence of a bad index, not termination, so it is a poor fit for termination benchmarks.

### Cited Findings
- `TermCOMP/TPDB` (last push 2025-08-20): code search for "hofstadter", "f91", "mc91" and "mccarthy" returned 0 hits. **[V]** [TPDB](https://github.com/TermCOMP/TPDB)
  - Coverage caveat: code search also failed to find a known string in an archived repo (§10). TPDB problems use TRS/ITS formats with arbitrary function names, so a McCarthy-91-style problem could exist under another name.
- Lean's and Isabelle's standard "hard nested termination" example is McCarthy 91, not Q. **[V]** [Lean thread](https://github.com/leanprover-community/archive/blob/master/zulip_json/270676-lean4/McCarthy.2091.20function.20using.20partial_fixpoint.json), [Isabelle Functions.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Examples/Functions.thy)

### Inferences
- **Termination is trivial under convention.** Under any convention that returns a positive value at indices ≤ 0 (e.g. Wolfram's f(n)=1 for n ≤ 0, per the coordinator's notes), Q's recursion trivially terminates: outputs are ≥ 1, so lookback indices strictly decrease. A termination tool would only need the output-positivity invariant.
- **Failure is a safety property.** Under Hofstadter's original convention, failure means reaching index ≤ 0 (a "runtime error"), which is a safety or reachability property. It would belong in software-verification benchmarks such as SV-COMP, and I did not search those.
- **Padding with 0 can create non-termination.** Q(n) = Q(n − 0) + … calls itself, so the padding convention matters when encoding Q for tools.

### Gaps
- I did not search AProVE example collections, SV-COMP or the termCOMP result pages directly.

## 8. Certified computation: is there a formally verified computation of Q terms? Is Mantovanelli's certificate machine-checked? Precedents

### Takeaway
No published proof-assistant-verified computation of Q values exists. The only formal-computation datapoints are the coordinator's own Lean experiments and an unpublished Lean check to 2·10^5 by the LLM audit.

Mantovanelli's certificate for the perturbed Q is plain Python and explicitly not a proof-assistant formalization. Cloitre's independent proof of the same result is a 50-page human combinatorial argument.

Methodological precedents for certified large computation: Coq-BB5 (Busy Beaver, 2024–2025) and Letouzey's verified tabulation of nested recurrences in Coq.

### Cited Findings
- **Zenodo record** "Supplementary Code and Certificate Data for 'Certified Return-Word Induction for a Perturbed Hofstadter Recursion'" (v3.0.0, created 2026-07-22, type: software, creator Marco Mantovanelli; one zip of 223,189 bytes). **[V]** [Zenodo 10.5281/zenodo.21495335](https://doi.org/10.5281/zenodo.21495335)
  - Contents: "the complete 122-rule transition kernel, the 92-state domain, … the block-lag potential, the C7 semantic checker, and the global-closure audit".
  - Running `python run_all_checks.py` executes nine checks and writes `"passed": true`. It requires CPython ≥ 3.11 and no third-party packages, and ships SHA-256 checksums.
  - "The package is not a Lean, Coq, Isabelle, or HOL formalization. The free-monoid gluing arguments and the final residual reconstruction remain human-readable mathematical arguments."
- **arXiv 2603.29622** (single author Mantovanelli; v1 2026-03-31, v2 2026-05-18, v3 2026-07-22; comments: "Major Revision. 27 pages, 3 figures"; MSC 11B37, 68Q45; 37B10, 03D25, 68Q60). The abstract describes "Exhaustive finite checks" and "a finite potential certificate", with no proof assistant. **[V]** [arXiv](https://arxiv.org/abs/2603.29622v3)
  - OEIS lists the paper under an intermediate title, "Certified Finite-State Induction for a Perturbed Hofstadter Recursion". **[V]** [OEIS A394051](https://oeis.org/A394051)
- **OEIS A394051** "Hofstadter Q-sequence perturbed by (-1)^n" (Mantovanelli, Mar 08 2026; entry created 2026-03-25). Comments: "All terms are odd"; "a(n) ~ n/2" numerically; "does not terminate for all n <= 3*10^10 (verified computationally)". It links arXiv 2603.16111 ("Dyadic Self-Similarity in a Perturbed Hofstadter Q-Recursion"), 2603.29622 and 2609.02412. **[V]** [OEIS A394051](https://oeis.org/A394051)
- **Cloitre**, "The Mantovanelli-Hofstadter Sequence" (earlier title "On a perturbed Hofstadter Q-recursion"), arXiv 2604.06237 (v1 2026-04-04, v3 2026-07-22, 50 pp.). It claims "We prove that this recurrence is well-defined for every positive integer" and Q̃(n)/n → 1/2, with n/2 + O(n/√log n). The method is combinatorial (binary words, Dyck paths, plane forests). The abstract mentions no proof assistant or code. **[V]** [arXiv](https://arxiv.org/abs/2604.06237)
- **Mantovanelli**, arXiv 2609.02412 (2026-09-02): a two-variable zeta function for the perturbed recursion. It has Zenodo reproducibility materials and no formal verification. **[V]** [arXiv](https://arxiv.org/abs/2609.02412)
- **LLM audit**: "A computation (scratch4.lean) reproduces A005185's first terms and confirms Q(n) ≤ n for n ≤ 200000". The method and code are unpublished. **[S]** [audit JSON](https://github.com/tadamcz/fc-review-results/blob/main/data/aea251bb26/files/ErdosProblems/422.json)
- **Precedent, Coq-BB5.** "Determination of the fifth Busy Beaver value" (bbchallenge Collaboration, arXiv 2509.12337) established S(5) = 47,176,870 in Coq by deciding halting for 181,385,789 machines. **[S]** [arXiv](https://arxiv.org/abs/2509.12337)
  - Announced 2024-07-02. Search summaries report about 13 h compile on a laptop at first, then about 45 min on 13 cores. **[S]** [bbchallenge forum](https://discuss.bbchallenge.org/t/july-2nd-2024-we-have-proved-bb-5-47-176-870/237)
- **Precedent, Letouzey `Fast.v`.** FlexArray tabulation of nested recurrences with proven equality to the spec (`f_spec`). **[V]** [Fast.v](https://github.com/letouzey/hofstadter_g/blob/main/Fast.v)
- **Automated, non-ITP precedent, Nathan Fox.** "Finding Linear-Recurrent Solutions to Hofstadter-Like Recurrences Using Symbolic Computation" (arXiv 1609.06342) gives a symbolic algorithm that finds and proves eventually linear-recurrent solutions; "hundreds of easy to describe families based on the Hofstadter Q-recurrence alone". There is also Fox's JIS 2024 three-term analogue (arXiv 2406.00904), and his Rutgers thesis on automatically proven solutions. **[S]** [arXiv 1609.06342](https://ar5iv.arxiv.org/html/1609.06342), [arXiv 2406.00904](https://arxiv.org/abs/2406.00904), [thesis](https://sites.math.rutgers.edu/~zeilberg/Theses/NathanFoxThesis.pdf)

### Inferences
- Proving the perturbed-Q result (Mantovanelli's certificate route or Cloitre's combinatorial route) in Lean would be the first machine-checked totality proof for any Q-type recurrence with chaotic or unknown totality status. Mantovanelli's finite certificate, a 122-rule kernel over 92 states, looks well suited to `decide`/`native_decide`-style checking plus a hand-formalized "gluing" lemma.
- For unperturbed Q, a Lean verification of Q(n) ≤ n to large N is not in the literature. The coordinator's kernel benchmark (about 10^4) and native result (10^7) already exceed every published formal computation I found.

### Gaps
- I did not download the Zenodo zip, so I can't say how much of the paper's argument the nine checks cover beyond the record description.
- I did not read Cloitre's full PDF to see whether he relies on any computation.

## 9. Lean Zulip: threads mentioning Hofstadter, meta-Fibonacci, A005185 or Erdős 422?

### Takeaway
The public Zulip archive has no thread on Hofstadter's Q, A005185, meta-Fibonacci or Erdős 422. "Hofstadter" appears only for the Figure-Figure sequences (2019, nothing formalized), the GEB MIU system, and personal reminiscences. The one directly useful thread is the 2025 McCarthy 91 `partial_fixpoint` recipe (§5).

### Cited Findings
- The Zulip API requires authentication, even for web-public channels. I instead searched the public archive's backing repo `leanprover-community/archive` (directory `zulip_json`). **[V]** [archive repo](https://github.com/leanprover-community/archive)
- "Hofstadter" hits in the archive **[V]**:
  - #maths "complementary sequences" (2019-09-03): Johan Commelin asks "Can we define the Figure Figure sequences?". Floris van Doorn suggests a mutual definition; Patrick Massot and Kevin Buzzard discuss whether it is interesting. Nothing was formalized. [thread](https://leanprover-community.github.io/archive/stream/116395-maths/topic/complementary.20sequences.html)
  - #maths "What's new in Lean maths?" (2020-08-19, rss-bot): mathlib PR #3739 formalizing the MIU language "described by D. Hofstadter". [archive JSON](https://github.com/leanprover-community/archive/blob/master/zulip_json/116395-maths/What's.20new.20in.20Lean.20maths.3F.json)
  - #general "MIU formal system".
  - #general "Interactive Learning Materials" (2023): the MIU game.
  - #new members (2023-11-23): a reminiscence about Hofstadter's books.
- Archive searches for "A005185", "meta-Fibonacci" and "Erdos 422" return 0 hits. "McCarthy 91" finds the #lean4 thread "McCarthy 91 function using partial_fixpoint" (2025-02-20). **[V]** [thread JSON](https://github.com/leanprover-community/archive/blob/master/zulip_json/270676-lean4/McCarthy.2091.20function.20using.20partial_fixpoint.json)

### Inferences
- No Lean community discussion of formalizing Q's totality appears to exist publicly. A Zulip post could be a natural venue to coordinate with the formal-conjectures maintainers, given open issue #6544.

### Gaps
- Private or non-web-public Zulip streams (and DMs) were not searchable.
- GitHub code search of a 200 MB repo may not index every JSON file, so "0 hits" is strong but not conclusive.

## 10. Other systems: HOL4/HOL Light, ACL2, Agda, Metamath, Mizar, PVS, plus Dafny and Why3

### Takeaway
Outside Lean and Coq, the only Hofstadter-sequence formal artifacts are teaching-style termination proofs of Hofstadter's Female/Male (and G) in Why3 and Dafny. Their technique, putting the bound f(n) ≤ n in the postcondition so the nested call's variant decreases, is the standard pattern, and it is exactly what is unavailable for Q. Metamath's "Hofstadter" content is only the MIU system. No hits were found for ACL2, HOL4, HOL Light, PVS, Mizar or Agda, but code-search coverage there is weak.

### Cited Findings
- **Why3.** `examples/mutual_recursion.mlw` (added 2020-05-01 by Jean-Christophe Filliâtre) contains "Hofstadter's Female and Male sequences" as `let rec function f … variant {n, 1} ensures {if n = 0 then result = 1 else 1 <= result <= n}` with `m … ensures {… 0 <= result < n}`. It is preceded by an example credited to Leino's book "Program Proofs". **[V]** [mutual_recursion.mlw](https://github.com/AdaCore/why3/blob/master/examples/mutual_recursion.mlw)
- **Dafny.** A reader's solutions to "Program Proofs" (repo 2023-03-23) label Exercise 3.15 "Hofstadter Female and Male Sequences", with `decreases n, 1` / `decreases n, 0`. **[V]** [ch3.dfy](https://github.com/benjaminfjones/stunning-palm-tree/blob/main/ch3.dfy)
  - A 2026 Kotlin port (SnaKt) says the book's Dafny source includes Hofstadter G with a `// decreases ...?` placeholder, calling these "the canonical example of functions whose termination is extremely difficult to prove formally". That is the porter's commentary. **[S]** [3_Hofstadter.kt](https://github.com/pawinkler/snakt-program-proofs/blob/main/part0_learning_the_ropes/chapter03_recursion_and_termination/examples/3_Hofstadter.kt)
- **Metamath.** Code search for "hofstadter" in `.mm` files finds only `miu.mm` (the MIU system) in set.mm and its forks and tools. **[V]** [metamath/set.mm](https://github.com/metamath/set.mm)
- **Agda.** `.lagda` hits are only the Löb paper (a GEB mention). The classical type-theory approach to nested partial recursion is Bove–Capretta (§3). **[V]** [lob.lagda](https://github.com/JasonGross/lob-paper)
- **HOL4, HOL Light, ACL2, PVS.** Code search for "Hofstadter" in `HOL-Theorem-Prover/HOL`, `jrh13/hol-light`, `acl2/acl2` and `nasa/pvslib` returned 0 hits. **[V]** [HOL4](https://github.com/HOL-Theorem-Prover/HOL), [ACL2](https://github.com/acl2/acl2)
  - **Coverage caveat:** the same search on the archived `leanprover-community/mathlib3`, whose `archive/miu_language` certainly mentions Hofstadter, also returned 0 hits. So these negatives are weak.
- **Mizar.** Code search with `extension:miz` returned 0 hits. The Mizar Mathematical Library could not be searched directly. **[V]** (search only)
- **HOL4-adjacent OEIS work.** The Gauthier–Urban synthesized programs (AAAI-23) for A005206 (G) and A005378 (Female) are the source of sequencelib's Lean entries (§2). **[V]** [A005378.lean](https://github.com/provables/sequencelib/blob/main/Sequencelib/Synthetic/A005/A005378.lean)

### Inferences
- **Dafny and Why3.** These systems would face the same obstacle as Lean or Coq. Proving termination of Q's nested calls needs a postcondition like 1 ≤ Q(n) ≤ n. The lower bound is easy; the upper bound is the open problem. Without the upper bound, the encoding must permit failure.

### Gaps
- I could not search the Mizar MML, ACL2 community books, HOL Light or PVS NASALib reliably for Hofstadter, Conway or McCarthy content, given the GitHub code-search coverage limits.
- No local clones were made (per constraints).
