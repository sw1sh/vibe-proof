# Rule 30 Prize: Lean snapshot

This folder holds the Lean results of the 2026-10-15 attempt on the Rule 30 Prize as a standalone Lake project. It is a snapshot of the `ruliology-lean` catalog (`vibe-proof/ruliology-lean`, which git does not track), taken on 2026-10-15.

**Problem 1 is still open.** These are partial results. [`../README.md`](../README.md) gives the status by period, and [`../writeup/rule30-state.html`](../writeup/rule30-state.html) is the full write-up.

- **Copied modules (54):** the 40 `Rule30*` modules that the catalog root imports, plus their import closure. The closure adds the 13 data modules in `Rule30Certificates/` and `BusyBeaverLifetimes`, which `Rule30Blocks` imports.
  - All 54 are byte-identical copies, at their catalog paths.
  - `SHA256SUMS` lists their hashes. Each one equals the catalog file's hash at copy time and the integration manifest `../research/integrate-final/catalog_after.sha256`.
  - To recheck the files, run `shasum -a 256 -c SHA256SUMS`.
- **Added here:**
  - `Ruliology.lean`: the root, importing the 40 modules in the catalog root's order;
  - `lakefile.toml`: package `rule30prize`, library `Ruliology`;
  - `lean-toolchain`: the same as the catalog;
  - `lake-manifest.json`, written by Lake;
  - `SHA256SUMS` and this README.
- **Lean:** core Lean 4.30.0. There is no Mathlib and no other dependency, and no `sorry` or `native_decide`.
- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound`. This was checked on 2026-10-15 in two ways:
  - `#print axioms` on 15 headline theorems: `center_not_eventually_period_one`, `no_column_eventually_constant`, `no_small_eventual_period`, `transient_add_period_ge`, `not_eventually_period_two_of_Q01`, `q01_width_le_52`, `free_bit_constraints` (width 6), `absorption_excludes`, `least_period_four_of_absorption`, the three `pure_ether_not_in_trap_*`, `no_wall_le_12`, `not_eventually_001_of_absorption` and `not_eventually_011_of_C3w`;
  - `Lean.collectAxioms` on all 5,353 constants of the 55 `Ruliology` modules (the 54 copies and the root), with 0 violations.

## Building

You need [elan](https://github.com/leanprover/elan); it installs Lean 4.30.0 from `lean-toolchain`.

`lake build` builds everything, but a cold build runs modules in parallel. The four `Rule30Certificates/ZeroBoundaryWidth52Chunks*` modules take about 20 s and 3 GB each, so a cold parallel build can need about 12.5 GB.

Building one module at a time is safest; each `lake build` below compiles exactly one module, and peak memory stays under 4 GB.

```sh
cd VibeProof/Rule30Prize/lean
for m in Rule30Predecessors Rule30PredecessorCounts BusyBeaverLifetimes Rule30Blocks Rule30Jen \
    Rule30Prize Rule30Window Rule30MaskedJen Rule30Diagonals Rule30BlackRuns Rule30BlackRunBlocks \
    Rule30StripCertificates Rule30StripCertificateTable Rule30DrivenLeft Rule30RightPeriods \
    Rule30WhiteSeed Rule30Realization Rule30FactorWindow Rule30PeriodTwo Rule30ZeroBoundary \
    Rule30ZeroBoundaryStripe Rule30ZeroBoundarySmall Rule30ZeroBoundaryBarriers Rule30Ether \
    Rule30PeriodTwoCoupled Rule30PeriodFourSkeleton Rule30ZeroBoundaryLanes \
    Rule30Certificates.ZeroBoundaryWidth52Chunks{0,1,2,3} Rule30ZeroBoundaryWidth52 \
    Rule30ZeroBoundaryStripeFront Rule30Certificates.ZeroBoundaryStripeCycles{0,1,2} \
    Rule30ZeroBoundaryStripeFamily Rule30EtherTrap Rule30Certificates.EtherTrap{0,1,2,3,4,5} \
    Rule30EtherTrapWidth20 Rule30PeriodTwoLanguage Rule30PeriodTwoWidth5 Rule30PeriodTwoWidth6 \
    Rule30EtherThree Rule30EtherThreeNoWall Rule30EtherThreeTrap Rule30EtherThreeReach \
    Rule30EtherThreeLeft Rule30EtherThreeSkeleton; do
  lake build Ruliology.CellularAutomata.$m || break
done
lake build
```

On 2026-10-15 this took 285 s in total on an Apple M3 Max with 48 GB. Every module not listed below built in under 7 s and 1.2 GB.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | 22–24 s each | 2.7–2.8 GB each |
| `Rule30StripCertificateTable` | 21 s | 3.9 GB |
| `Rule30BlackRunBlocks` | 20 s | 2.3 GB |
| `Rule30ZeroBoundarySmall` | 19 s | 3.2 GB |
| `Rule30ZeroBoundaryStripe` | 18 s | 1.8 GB |
| `Rule30EtherThreeNoWall` | 9 s | 1.1 GB |
| `Rule30BlackRuns` | 9 s | 2.2 GB |

`Rule30PeriodTwoLanguage` prints five "This simp argument is unused" linter warnings (line 169). The catalog build prints the same five, and Lake repeats them when it builds later targets.

To check axioms, compile a file outside this folder from here:

```sh
cat > /tmp/Axioms.lean <<'EOF'
import Ruliology
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_period_one
EOF
lake env lean /tmp/Axioms.lean
```

## Which modules predate the attempt

The birth times of the catalog files (`stat -f %B`) and the docstrings agree. The *Added* column of the tables below uses these labels.

| Added | When | Modules |
|---|---|---|
| `10-10` | 2026-10-10 | Five catalog entries from Wolfram's writings, written before the attempt: `Rule30Predecessors`, `Rule30PredecessorCounts`, `BusyBeaverLifetimes`, `Rule30Blocks`, `Rule30Jen`. Their docstrings cite only Wolfram and the literature. |
| `start` | 2026-10-15, 04:07–04:16 | The first Rule 30 Prize modules, written before the multi-agent rounds: `Rule30Prize`, `Rule30Diagonals`, `Rule30Window`. Their docstrings do not cite the multi-agent project. |
| `R1`, `R2`, `final` | 2026-10-15, 07:18, 09:40, 11:49 | The other 46 modules: round 1 (11), round 2 (7) and the final batch (28, including the 13 in `Rule30Certificates/`). Their docstrings cite the Rule 30 Prize project (2026). |

## Modules by topic

All modules live in `Ruliology/CellularAutomata/`. Theorems live in the namespace `Ruliology.CellularAutomata.<Module>`, with these exceptions:

- `Rule30Predecessors` and `Rule30PredecessorCounts` use `…Rule30`.
- The six `Rule30EtherThree*` modules share `…Rule30EtherThree`.
- `Rule30EtherTrapWidth20` uses `…Rule30EtherTrap`.
- `Rule30ZeroBoundaryStripeFamily` uses `…Rule30ZeroBoundaryStripeFront`.
- The data modules in `Rule30Certificates/` use namespaces inside the module they serve, for example `…Rule30ZeroBoundaryWidth52.C0`.

"Open" marks a statement defined as a `Prop` but not proved.

### Period 1

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Prize` | start | States Problems 1 and 2 as in formal-conjectures' `Other/Rule30.lean`. No column is eventually constant, so period 1 is excluded for every column and every transient. | `Problem1`, `Problem2`, `no_column_eventually_constant`, `center_not_eventually_period_one` |

### Windows

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Window` | start | From the first 16,384 center bits, computed in the kernel: there is no eventual period P ≤ 4096 with transient ≤ 8192. | `no_small_eventual_period` |
| `Rule30FactorWindow` | R1 | Any eventual period P from time T has T + P ≥ 16359, because the first 16,384 bits have 16,359 distinct factors of length 26. | `transient_add_period_ge` |

### Black runs and strip certificates

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30BlackRuns` | R1 | Nine black cells in a column shield the right half (Lemma A). Long black runs exclude many periods (Theorems B and D). | `nine_black`, `black_shield`, `no_long_black_run`, `no_black_white_run`, `not_eventually_zero_ones`, `no_white_run_11` |
| `Rule30BlackRunBlocks` | R1 | Theorem B′: excludes repeating words `1^r u` for eight kernel-checked blocks `u`, provided the black run is long: `r ≥ 18` for `u = 0, 00, 000, 0000, 0100`, and `r ≥ 27` for `u = 010, 0010, 0110`. Short runs, such as the open words `10`, `100` and `1110`, are not covered. | `no_black_run_block`, `no_period_black_run_then_white` |
| `Rule30StripCertificates` | R1 | Problem 1 holds iff no word is an eventual tail. Bitmask and rank strip certificates are sound via masked Jen; three words are excluded. | `problem1_iff_no_word`, `not_eventually_word_strip`, `Cert.sound`, `not_eventually_00000011`, `not_eventually_000000000101` |
| `Rule30StripCertificateTable` | R1 | Kernel-checked certificates exclude 30 periodic words of length 8–13. | `not_eventually_certTable` |

### Jen and masked Jen

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Jen` | 10-10 | Jen (1986): no two columns are both eventually periodic. | `jen`, `periodic_column_unique`, `not_adjacent` |
| `Rule30MaskedJen` | R1 | Masked, effective-boundary and window forms of Jen's theorem. | `masked_jen`, `orCol_not_eventuallyPeriodic`, `effective_step`, `window_jen`, `finitary_jen` |
| `Rule30DrivenLeft` | R1 | Jen's theorem for the left half driven by a boundary column: from a finite nonzero start, an eventually periodic driver makes no left column eventually periodic. A barrier: for a start whose leftmost black cell is at −n, column −1 can follow any target for the first n − 1 steps. | `no_periodic_column`, `barrier_exists`, `barrier_unique` |
| `Rule30WhiteSeed` | R1 | Of the center columns from a single black cell and from a single white cell, at least one is not eventually periodic. The same holds for rules 30 and 135. | `problem1_black_or_white`, `problem1_30_or_135` |

### Diagonals

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Diagonals` | start | Right diagonals have period 2^j from the start, and left diagonals are eventually 2^j-periodic. | `R_periodic`, `D_periodic`, `center_eq_parity` |
| `Rule30RightPeriods` | R1 | Right-diagonal periods: the doubling rule, upper and lower bounds, rows at powers of two, restarts. | `e_step`, `per_bound`, `per_upper`, `rows_at_powers_of_two`, `not_half_lower` |

### Zero-boundary left half and period 2

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30PeriodTwo` | R1 | What an eventual period 2 forces. `Q01` (zero-driven left half; **open**) implies no eventual period 2. | `normalize`, `golden`, `not_eventually_period_two_of_Q01`, `stripe_fixed` |
| `Rule30ZeroBoundary` | R2 | The zero-boundary left half (ZBL): dynamics, realization, free bits, equivalent forms of `Q01`, Jen inside the ZBL. | `Q01_iff_Theta`, `Q01_iff_bounded`, `Q01_iff_staged`, `count_constrained`, `jen_clock`, `free_bits_no00_no11111` |
| `Rule30ZeroBoundaryStripe` | R2 | ZBL epochs, stripe stability and stripe absorption. | `stripe_absorb`, `Theta_eventually_stripe_iff`, `first_defect_phase` |
| `Rule30ZeroBoundarySmall` | R2 | `Q01` holds for every start of width ≤ 16 (kernel-checked search). | `q01_width_le_16`, `q01_width_le_15_odd` |
| `Rule30ZeroBoundaryLanes` | final | A bit-sliced `Q01` checker that runs in the kernel, with its soundness proof. | `q01_of_checks`, `q01_of_chunks` |
| `Rule30ZeroBoundaryWidth52` | final | `Q01` holds for every start of width ≤ 52: depth 1 turns white at an even time ≤ 96. | `q01_width_le_52`, `q01_width_le_52_linear`, `not_inX_of_width_le_52` |
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | final | Data: the 256 chunk checks behind width 52, 64 per file (namespaces `Rule30ZeroBoundaryWidth52.C0`–`C15`). | — |
| `Rule30ZeroBoundaryStripeFront` | final | The front window of a stripe prefix evolves on its own; checked periodic orbits bound its death time. | `front_sound`, `family_of_class` |
| `Rule30ZeroBoundaryStripeFamily` | final | Every stripe prefix `S[1..m] · v · 0^∞` with \|v\| ≤ 3 dies within 31 steps of arrival. | `stripe_prefix_family`, `stripe_prefix_family_list` |
| `Rule30Certificates/ZeroBoundaryStripeCycles0`–`2` | final | Data: the eight window cycles behind the stripe-prefix family. | — |
| `Rule30PeriodTwoCoupled` | R2 | The coupled question `CQ01` (**open**): `Q01` implies `CQ01`, and `CQ01` excludes period 2. The ether is an infinite witness. | `CQ01_of_Q01`, `no_eventual_period_two_of_CQ01`, `ether_coupled_witness` |
| `Rule30PeriodTwoLanguage` | final | Under period 2: if a kernel check shows that no path inside the bad class of the right strip spells a word, then column 1 at the white times eventually never spells it. | `no_pattern` |
| `Rule30PeriodTwoWidth5` | final | Period-2 constraints at strip width 5; for example, the free bits never spell `00` or `11111`. | `col1_constraints`, `free_bit_constraints` |
| `Rule30PeriodTwoWidth6` | final | The same at strip width 6, with more forbidden patterns. | `col1_constraints`, `free_bit_constraints` |

Q01 is also kernel-checked for width ≤ 56 in [`../research/kernel-certify-r2/t1`](../research/kernel-certify-r2/t1). That check is not in the catalog because of its build cost: about 6 minutes.

### Ether and period 4

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Ether` | R2 | The 7×4 ether, the 109-state wall and the ether-and-wall traps. Absorption (**open**) excludes `0001`, `0011` and `0111`. | `ether_rule`, `trap_invariant`, `no_ether_wall_entry`, `absorption_excludes`, `least_period_four_of_absorption` |
| `Rule30PeriodFourSkeleton` | R2 | The right-half skeletons that least period 4 forces, and a reduction to the left-half statements `C3` (**open**). | `skeleton_0001`, `skeleton_0011`, `column_m1_0111`, `least_period_four_of_C3` |
| `Rule30EtherTrap` | final | Traps of the strip relaxation, and a certificate check that a path escapes them. | `word_lemma`, `escapes_of_certOK`, `not_trap_of_certOK` |
| `Rule30EtherTrapWidth20` | final | The pure ether lies in no trap of width ≤ 20. | `pure_ether_not_in_trap_0001`, `pure_ether_not_in_trap_0011`, `pure_ether_not_in_trap_0111` |
| `Rule30Certificates/EtherTrap0`–`5` | final | Data: the 24 certificates behind width 20. | — |

### Period 3

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30EtherThree` | final | The 12×3 ether and the ether-and-wall framework for period 3. | `ether3_rule`, `alignments_001_complete`, `alignments_011_complete`, `absorption3_excludes` |
| `Rule30EtherThreeNoWall` | final | The period-3 ether has no wall of width ≤ 12. | `no_wall_le_12` |
| `Rule30EtherThreeTrap` | final | `t001`, a 47-column trap of period 21. `AbsorptionT t001` (**open**) excludes `001`. | `trap_001`, `absorptionT_excludes`, `not_eventually_001_of_absorption` |
| `Rule30EtherThreeReach` | final | The empty right half reaches `t001` at time 1270. | `t001_reached`, `absorbed_empty` |
| `Rule30EtherThreeLeft` | final | Reductions to the left half: `Q001` for `001` and `C3w` for `011` (both **open**). | `not_eventually_001_of_Q001`, `not_eventually_011_of_C3w`, `Q001_stripe`, `C3w_011_ether` |
| `Rule30EtherThreeSkeleton` | final | Right-half skeletons for `001` and `011`, and the reduction `C3s001` (**open**). | `skeleton_001`, `skeleton_011`, `not_eventually_001_of_C3s` |

### Barriers

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Realization` | R1 | Some configuration realizes any right half together with any column 0. Rules 90, 150 and 210 meet Jen's hypotheses, yet their center columns are eventually constant. | `column_realizable_unique`, `seed_perturbation`, `barrier` |
| `Rule30ZeroBoundaryBarriers` | R2 | For `Q01` there is no ranking through a finite abstraction, no local ranking and no edge-DFA ranking. Also gives a two-sided barrier. | `finite_abstraction_has_lasso`, `no_local_ranking`, `no_edge_dfa_ranking`, `no_joint_local_ranking` |

### Other catalog entries (not about Problem 1)

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Predecessors` | 10-10 | A corrected form of the Feynmans' predecessor theorem: rule 30 on a cyclic register. | `predCount_eq_three_iff`, `predCount_eq_one_iff` |
| `Rule30PredecessorCounts` | 10-10 | How many registers have 0, 1, 2 or 3 predecessors. | `sum_predCount`, `numWithPreds_zero` |
| `Rule30Blocks` | 10-10 | Only 24 of the 32 possible 3×2 blocks occur. | `blockAt_allowed`, `occurs_iff`, `occurs_single_cell` |
| `BusyBeaverLifetimes` | 10-10 | Busy-beaver lifetimes of four cellular automata. `Rule30Blocks` reuses its bit-plane simulation. | `lifetime450504084`, `lifetime5810255963295` |
