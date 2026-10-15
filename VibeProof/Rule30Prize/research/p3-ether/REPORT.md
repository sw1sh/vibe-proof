# p3-ether — final batch report (2026-10-15)

> **Note (coordinator).** This file was written from the worker's and verifier's structured output, so lines saying REPORT.md or VERDICT.md "was not written" refer to the agents' own attempts. Paths under `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/` point at the scratch area this folder was copied from; the same files are under `VibeProof/Rule30Prize/research/`.


Written by the coordinator from the worker's structured output (the harness blocked subagent report files).

## Summary

I did not write REPORT.md: the harness blocks report files from subagents, so the full report is in these fields. The Lean files and computation outputs are in /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/ (lean/ for modules, build/ for oleans, c/ for programs and runs). Nothing in the Ruliology repo or under ruliology-lean/Ruliology/ was modified. No processes are left running.

Main finding: least period 3 does not behave uniformly. The word 001 behaves like period 4: every right half tested is absorbed. But it is absorbed into a new trap, not an ether-and-wall family, and about 100 times more slowly. The word 011 behaves like 0101 or worse: column 1 never became periodic at the white times in any run.

1. Ether (Lean). The 12x3 ether is defined and proved to be a rule-30 orbit (ether3_rule), with a glide symmetry: shifting 4 columns equals shifting 1 step in time (ether3_glide). All six alignments of each word are proved, and they are proved complete (no others exist):
   - 001: (0,0), (1,0), (4,2), (5,2), (8,1), (9,1)
   - 011: (2,0), (3,2), (6,2), (7,1), (10,1), (11,0)

2. Walls.
   - The ether-and-wall framework is built generically in the wall W: WallOK (U-property plus closure over packed bit-mask strips), trap_invariant3, ether_wall_trap3, Absorption3, absorption3_excludes, and corollaries for 001 and 011.
   - However, no wall exists. no_wall_le_12 is a Lean kernel certificate: no attachment column has a wall of width 12 or less. An exhaustive C search (iterative Tarjan) finds none up to width 23. A closure probe finds none up to width 28. At each of these widths the strip relaxation has a unique minimal closed set, and it violates the U-property.
   - The search program was validated by reproducing the period-4 109-state wall at width 13.
   - So the period-3 ether-and-wall family is empty, and Absorption3 is vacuous for walls of width 12 or less.

3. A new trap for 001. t001 is a period-21 trap: 815 labelled states of a 47-cell strip next to the center.
   - It is closed under both inputs at column 48, and column 1 at the white phases is a fixed function of a time label mod 21.
   - Its first 38 columns are a breathing period-21 core containing a temporary black-ended stripe. It is not the ether (0 columns match in any alignment).
   - The closure is kernel-checked from packed tables (t001_check). trap_001 proves that entering the trap after the center becomes 001-periodic contradicts masked Jen. absorptionT_excludes and not_eventually_001_of_absorption prove that AbsorptionT t001 rules out a 001 tail.
   - t001_reached is a 1270-step kernel computation showing the empty right half actually reaches the trap.

4. Empirics (C, cross-checked against an independent exact Python simulation in 10 cases).
   - For 001, all 12,288 runs enter t001 (support in [1,12], 3 phases). Cumulative entry: 50.6% by 16,384 steps, 83.8% by 40,000, 99.49% by 120,000, 100% by 300,000. Maximum delay 186,490.
   - For 001, all 5,970 true right halves enter t001 (T = 1..1000, plus T = 1100..100000 in steps of 100, 3 phases). Maximum delay 201,756. Random halves of width 64: 83.6% within 40,000.
   - No run showed column 1 periodic at the white times without entering t001.
   - For 011: 0 periodic out of 12,288 small supports, 5,970 true halves and 900 random halves (horizon 20,000; also 0 of 48 at horizon 100,000).
   - The simulated center column matches center-1e7.bin for all t up to 100,000.
   - Round 2 for comparison: 0001, 0011, 0111 always absorbed (max delays 1017, 1869, 829); 0101 about 3%.

5. Left side (Lean reductions).
   - For 001 the effective boundary is 000, so the left half is the zero-boundary left half (ZBL).
     - Column -1 is (= column 1, not column 1, black) at phases 0, 1, 2.
     - Q001 (no ZBL start with a leftmost black cell keeps column -1 black every third step) rules out a 001 tail.
     - C3s001 (no finite ZBL start keeps column -1 = (0,*,1) eventually; uses the skeleton) also rules out a 001 tail.
   - For 011 the effective boundary is 010.
     - Column -1 is (not column 1, white, black).
     - C3w 011 (no finite start driven by 010 keeps column -1 = (*,0,1) eventually) rules out a 011 tail.
   - Finiteness is essential in both: the infinite stripe satisfies the Q001 constraint forever, and the infinite left part of the ether satisfies the C3w 011 constraint forever (both in Lean).
   - Exhaustive death-time search (C; reproduces A-monovariant/dfs.c on Q01 for W = 1..22 and matches brute force on 12 cases):
     - Q001: every start of width W ≤ 37 violates by time 94.
     - C3s001: every start of width W ≤ 70 violates by time 103.
     - C3w 011: every start of width W ≤ 70 violates by time 99.

6. Skeletons (Lean, bad-class certificates using the catalog's Cert.sound_bad).
   - skeleton_001: column 1 is eventually white at phase 0 (certificate width 4). Nothing more is forced up to width 13.
   - skeleton_011: column 1 is eventually black at phase 1 and white at phase 2 (certificate width 3). Nothing more is forced up to width 10.

Nothing unconditional about period 3 follows; this was not expected. Excluding least period 3 needs both one of the 001 statements (AbsorptionT t001, Q001 or C3s001) and C3w 011. All of these are open.

Lean build details:
- Six modules: P3Ether, P3NoWall, P3Trap001, P3Reach, P3Left, P3Skel.
- Build with lean/mk.sh; modules import each other through oleans in lean/build.
- Compile times and peak memory: 1.07 s / 0.60 GB, 8.84 s / 1.13 GB, 0.97 s / 0.64 GB, 0.37 s / 0.50 GB, 0.75 s / 0.56 GB, 0.43 s / 0.51 GB.
- No sorry, no native_decide.
- Negative controls (one corrupted table bit, skeleton predicate, or state index) make the kernel checks fail.
- The axiom output is saved in lean/axioms_output.txt and the pretty-printed statements in lean/checks_output.txt.

## Lean theorems (compiled by the worker; re-verified independently)

### `Ruliology.CellularAutomata.Rule30EtherThree.ether3_rule`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
∀ (j φ : Nat), ether3 j (φ + 1) = rule (ether3 (j + 11) φ) (ether3 j φ) (ether3 (j + 1) φ)
```

The 12x3 ether (columns 001 001 011 110 010 010 110 101 100 100 101 011 at phases 0..2) is a rule-30 orbit.

### `Ruliology.CellularAutomata.Rule30EtherThree.ether3_glide`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
∀ (j φ : Nat), ether3 (j + 4) φ = ether3 j (φ + 1)
```

Glide symmetry: four columns to the right equals one step later.

### `Ruliology.CellularAutomata.Rule30EtherThree.alignments_001_complete`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
∀ (j0 : Nat), j0 < 12 → ∀ (s : Nat), s < 3 → (aligned3 w001 j0 s = true ↔ (j0, s) ∈ A001), A001 = [(0,0),(1,0),(4,2),(5,2),(8,1),(9,1)]
```

001 is ether column j0 shifted by s exactly for these six pairs. Each pair also has its own aligned3_001_* theorem.

### `Ruliology.CellularAutomata.Rule30EtherThree.alignments_011_complete`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
∀ (j0 : Nat), j0 < 12 → ∀ (s : Nat), s < 3 → (aligned3 w011 j0 s = true ↔ (j0, s) ∈ A011), A011 = [(2,0),(3,2),(6,2),(7,1),(10,1),(11,0)]
```

All six alignments of 011, and no others.

### `Ruliology.CellularAutomata.Rule30EtherThree.trap_invariant3`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
IsR30 F → WallOK a b W → 0 < b → ∀ j0 s k t1, (j0+k)%12 = a%12 → (∀ t ≥ t1, F t 0 = ether3 j0 (t+s)) → (∀ p, 1≤p → p≤k → F t1 p = ether3 (j0+p) (t1+s)) → ∀ r, EncF F b t1 k r → W ((t1+s)%3) r → ∀ n, (∀ p ≤ k, F (t1+n) p = ether3 (j0+p) (t1+n+s)) ∧ ∃ r', EncF F b (t1+n) k r' ∧ W ((t1+n+s)%3) r'
```

Ether segment plus wall is invariant, for any wall W satisfying WallOK (U-property plus closure over bit-mask strips).

### `Ruliology.CellularAutomata.Rule30EtherThree.ether_wall_trap3`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
WallOK a b W → 0 < b → ∀ T t1 j0 s k, (j0+k)%12 = a%12 → (∀ t ≥ T, cell t 0 = ether3 j0 (t-T+s)) → T ≤ t1 → (∀ p, 1≤p → p≤k → cell t1 p = ether3 (j0+p) (t1-T+s)) → ∀ r, EncF trueRight b t1 k r → W ((t1-T+s)%3) r → False
```

Period-3 ether-and-wall trap for the true pattern (by masked Jen with P = 3).

### `Ruliology.CellularAutomata.Rule30EtherThree.absorption3_excludes`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Ether.lean`
- axioms: [propext, Quot.sound]
- compile: 1.07 s

```lean
(∀ al ∈ A, aligned3 w al.1 al.2 = true) → WallOK a b W → 0 < b → Absorption3 w A a b W → ¬∃ T, ∀ t ≥ T, cell t 0 = wordAt3 w (t - T)
```

Absorption into the ether-and-wall family rules out a w tail. not_eventually_001_of_absorption3 and not_eventually_011_of_absorption3 are the instances for 001 and 011. Vacuous for walls of width 12 or less, since none exist.

### `Ruliology.CellularAutomata.Rule30EtherThree.no_wall_le_12`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3NoWall.lean`
- axioms: [propext, Quot.sound]
- compile: 8.84 s

```lean
∀ (a b : Nat), 0 < b → b ≤ 12 → ∀ {W : Nat → Nat → Prop}, WallOK a b W → ∀ (φ r : Nat), ¬W φ r
```

No ether wall of width 12 or less exists at any attachment column. Uses walls lifting to wider strips, a glide reduction to columns 0..3, and four kernel-checked distance-to-violation certificates over all 3*4096 states.

### `Ruliology.CellularAutomata.Rule30EtherThree.t001_check`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Trap001.lean`
- axioms: [propext]
- compile: 0.97 s

```lean
PTrap.check t001 = true
```

The 815-state, width-47, label-mod-21 trap for 001 is closed under both inputs, has consistent labels, and column 1 at white phases equals u(label). Kernel-checked from packed bit-mask tables.

### `Ruliology.CellularAutomata.Rule30EtherThree.PTrap.trap`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Trap001.lean`
- axioms: [propext, Quot.sound]
- compile: 0.97 s

```lean
PTrap.check C = true → 0 < C.b → ∀ T, (∀ t ≥ T, cell t 0 = wordAt3 C.w (t - T)) → ∀ t1 i, T ≤ t1 → i < C.n → (t1 - T) % 3 = C.lab i % 3 → EncF trueRight C.b t1 0 (C.st i) → False
```

Entering any checked labelled trap after the center became w-periodic contradicts masked Jen (P = m).

### `Ruliology.CellularAutomata.Rule30EtherThree.trap_001`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Trap001.lean`
- axioms: [propext, Quot.sound]
- compile: 0.97 s

```lean
∀ T, (∀ t ≥ T, cell t 0 = wordAt3 w001 (t - T)) → ∀ t1 i, T ≤ t1 → i < t001.n → (t1 - T) % 3 = t001.lab i % 3 → EncF trueRight 47 t1 0 (t001.st i) → False
```

If the center is 001 from T and columns 1..47 ever form a t001 state with the matching phase, contradiction.

### `Ruliology.CellularAutomata.Rule30EtherThree.absorptionT_excludes`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Trap001.lean`
- axioms: [propext, Quot.sound]
- compile: 0.97 s

```lean
PTrap.check C = true → 0 < C.b → AbsorptionT C → ¬∃ T, ∀ t ≥ T, cell t 0 = wordAt3 C.w (t - T)
```

Absorption of every finite right half into a checked trap rules out a w tail.

### `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_absorption`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Trap001.lean`
- axioms: [propext, Quot.sound]
- compile: 0.97 s

```lean
AbsorptionT t001 → ¬∃ T, ∀ t ≥ T, cell t 0 = wordAt3 w001 (t - T)
```

If every finite right half driven by 001 enters t001, the center column is not eventually 001 (for any transient).

### `Ruliology.CellularAutomata.Rule30EtherThree.t001_reached`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Reach.lean`
- axioms: [propext, Quot.sound]
- compile: 0.37 s

```lean
∃ i, i < t001.n ∧ (1270 + 0) % 3 = t001.lab i % 3 ∧ EncF (drv (fun t => wordAt3 w001 (t + 0)) fun _ => false) t001.b 1270 0 (t001.st i)
```

The empty right half driven by 001 from phase 0 is in the trap at time 1270 (kernel computation plus rowN_eq_drv), so the trap is not vacuous.

### `Ruliology.CellularAutomata.Rule30EtherThree.col_m1_001`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Left.lean`
- axioms: [propext, Quot.sound]
- compile: 0.75 s

```lean
(∀ t ≥ T, cell t 0 = wordAt3 w001 (t-T)) → ∀ t ≥ T, ((t-T)%3=0 → cell t (-1) = cell t 1) ∧ ((t-T)%3=1 → cell t (-1) = !cell t 1) ∧ ((t-T)%3=2 → cell t (-1) = true)
```

Under 001, column -1 is forced black at the black phase and tied to column 1 at the white phases.

### `Ruliology.CellularAutomata.Rule30EtherThree.col_m1_011`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Left.lean`
- axioms: [propext, Quot.sound]
- compile: 0.75 s

```lean
(∀ t ≥ T, cell t 0 = wordAt3 w011 (t-T)) → ∀ t ≥ T, ((t-T)%3=0 → cell t (-1) = !cell t 1) ∧ ((t-T)%3=1 → cell t (-1) = false) ∧ ((t-T)%3=2 → cell t (-1) = true)
```

Under 011, column -1 is (not column 1, white, black).

### `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_Q001`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Left.lean`
- axioms: [propext, Quot.sound]
- compile: 0.75 s

```lean
Q001 → ¬∃ T, ∀ t ≥ T, cell t 0 = wordAt3 w001 (t - T), where Q001 := ∀ m s, 0 < m → (∀ p < -m, s p = false) → s (-m) = true → ¬ ∀ k, Rule30DrivenLeft.L (fun _ => false) s (3*k) (-1) = true
```

Reduction of 001 to the ZBL left-only problem Q001, the analog of Q01.

### `Ruliology.CellularAutomata.Rule30EtherThree.Q001_stripe`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Left.lean`
- axioms: [propext, Quot.sound]
- compile: 0.75 s

```lean
∀ (k : Nat), Rule30DrivenLeft.L (fun _ => false) Rule30PeriodTwo.stripe (3 * k) (-1) = true
```

Finiteness is essential in Q001: the infinite stripe satisfies the constraint forever.

### `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_011_of_C3w`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Left.lean`
- axioms: [propext, Quot.sound]
- compile: 0.75 s

```lean
C3w w011 → ¬∃ T, ∀ t ≥ T, cell t 0 = wordAt3 w011 (t - T), where C3w w := ∀ s, (∃ M, ∀ p < -M, s p = false) → ¬∃ K, ∀ k ≥ K, fits3 (colPattern3 w) (k % 3) (L (fun k => wordAt3 (effWord3 w) k) s k (-1)) = true; effWord3 w011 = 010, colPattern3 w011 = (*,0,1)
```

Reduction of 011 to the C3-type left-only problem with effective boundary 010.

### `Ruliology.CellularAutomata.Rule30EtherThree.C3w_011_ether`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Left.lean`
- axioms: [propext, Quot.sound]
- compile: 0.75 s

```lean
∀ (k : Nat), fits3 (colPattern3 w011) (k % 3) (Rule30DrivenLeft.L (fun k => wordAt3 (effWord3 w011) k) etherLeft k (-1)) = true
```

Finiteness is essential in C3w 011: the infinite left part of the ether is a solution forever.

### `Ruliology.CellularAutomata.Rule30EtherThree.skeleton_001`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Skel.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 0.43 s

```lean
∀ T, (∀ t ≥ T, cell t 0 = wordAt3 w001 (t - T)) → ∃ T', T ≤ T' ∧ ∀ t ≥ T', (t - T) % 3 = 0 → cell t 1 = false
```

Forced skeleton under eventual 001: column 1 eventually white at phase 0 (bad-class certificate, width 4, via Cert.sound_bad).

### `Ruliology.CellularAutomata.Rule30EtherThree.skeleton_011`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Skel.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 0.43 s

```lean
∀ T, (∀ t ≥ T, cell t 0 = wordAt3 w011 (t - T)) → ∃ T', T ≤ T' ∧ ∀ t ≥ T', ((t - T) % 3 = 1 → cell t 1 = true) ∧ ((t - T) % 3 = 2 → cell t 1 = false)
```

Forced skeleton under eventual 011: column 1 eventually black at phase 1 and white at phase 2 (certificate width 3).

### `Ruliology.CellularAutomata.Rule30EtherThree.col_m1_001_skeleton`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Skel.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 0.43 s

```lean
∀ T, (∀ t ≥ T, cell t 0 = wordAt3 w001 (t - T)) → ∃ T', T ≤ T' ∧ ∀ t ≥ T', ((t-T)%3=0 → cell t (-1) = false) ∧ ((t-T)%3=1 → cell t (-1) = !cell t 1) ∧ ((t-T)%3=2 → cell t (-1) = true)
```

Under eventual 001, column -1 is eventually (white, not column 1, black).

### `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_C3s`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/lean/P3Skel.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 0.43 s

```lean
C3s001 → ¬∃ T, ∀ t ≥ T, cell t 0 = wordAt3 w001 (t - T), where C3s001 := ∀ s, (∃ M, ∀ p < -M, s p = false) → ¬∃ K, ∀ k ≥ K, fits3 [some false, none, some true] (k % 3) (L (fun _ => false) s k (-1)) = true
```

Skeleton-strengthened left reduction for 001 (the C3 analog). The constraint (0,*,1) is stronger than Q001's, so C3s001 is the weaker, easier-to-prove statement.

## Computational results

- Wall search (c/wall3.c, iterative Tarjan, validated by reproducing the period-4 109-state wall at width 13): for all 12 attachment columns and every width b ≤ 23, the strip graph has exactly one minimal closed set and it violates the U-property. The maximal closed U-set is empty, so no ether wall exists. c/wall3b.c (random walk plus closure, matching Tarjan for b ≤ 23) finds the U-property violated for b = 24..28. Minimal closed set sizes grow about 1.58x per unit of width.
- Trap search (c/scc_an_copy.c): for both 001 and 011, at every strip width b ≤ 22 the unique minimal closed set of the strip driven by w is bad. So no trap of any kind (ether wall or otherwise) has width ≤ 22.
- Trap t001: the all-input closure of the observed 001 state (seed driven by c(0)=1 then 001, taken at T0=3000) has more than 5*10^6 states for b ≤ 46, exactly 815 at b = 47, and 1363..9590 for b = 48..52. Label mod 21 is consistent and column 1 at white times follows u = 01.00.00.00.00.00.01. C (c/closure.c) and Python (c/trap_export.py) agree. Seeds at 7 other times give the same 815 states. The core (columns 1..38) is not the 12x3 ether.
- 001 entry, support ⊆ [1,12], 3 phases (12,288 runs; c/entry3.c): cumulative entry 11.5% by 4,096 steps, 24.7% by 8,192, 50.6% by 16,384, 76.7% by 32,768, 83.8% by 40,000, 99.49% by 120,000, 100% by 300,000. Maximum delay 186,490. No run had column 1 periodic at white times without entering t001.
- 001 entry, true right halves (T = 1..1000 all, plus T = 1100..100000 in steps of 100, 3 phases; 5,970 runs): 84.7% within 40,000 steps and all 5,970 within 300,000. Maximum delay 201,756. Center column matches center-1e7.bin for t ≤ 100,000. Random width-64 halves: 83.6% within 40,000.
- Cross-validation: an independent exact Python simulation (c/xcheck_entry.py), using the trap decoded from the Lean data, reproduces entry3's entry times exactly in 10 cases (1270, 1269, 1265, 24433, 41933, 76457, plus true halves 15464, 2294, 25793, 14914).
- Strip relaxation at width 47 with i.i.d. random right inputs (c/rwalk47.c): 300 of 300 random strips enter t001 within 10^6 steps (mean 23,517, max 102,032). Entry is not forced for adversarial inputs.
- 011: column 1 at white times was never eventually periodic. 0/12,288 runs with support ⊆ [1,12] (horizon 20,000, periods up to 2,499 steps detectable), 0/48 with support ≤ 4 (horizon 100,000), 0/5,970 true halves, 0/900 random width-64 halves.
- Death-time searches (c/ldfs.c; reproduces A-monovariant/dfs.c on Q01 for W = 1..22 and matches c/lbrute.py brute force on 12 period-3 cases): Q001 (zero boundary, column -1 black every 3rd step) — every start of width W ≤ 37 violates by time 94 (max over the 3 phases; max/W 2.5..4). C3s001 (zero boundary, column -1 = (0,*,1)) — W ≤ 70 violates by time 103. C3w 011 (boundary 010, column -1 = (*,0,1)) — W ≤ 70 violates by time 99.
- Skeletons (c/skel_export3.py, which merges multiple bad SCCs into their convex hull): for 001, column 1 = 0 at phase 0 for b = 4..13 and nothing else. For 011, column 1 = (1 at phase 1, 0 at phase 2) for b = 3..10 and nothing else.
- Comparison with round 2: 0001, 0011, 0111 always absorbed (max delays 1017, 1869, 829); 0101 about 3%. Period 3: 001 always absorbed (into t001, delays up to about 2*10^5); 011 0% (column 1 never periodic).

## Gaps

- REPORT.md was NOT written: the harness refuses subagent report files ('Subagents should return findings as text'), and I did not work around it. Everything that file would contain is in this structured output. The supporting artifacts are on disk: lean/axioms_output.txt, lean/checks_output.txt, c/runs/*.
- No ether wall exists for widths ≤ 12 (Lean) or ≤ 23 (exhaustive C). So Absorption3 is false for every such wall, and absorption3_excludes and its 001/011 corollaries are vacuous there. Whether a wall exists at width > 28 is open; the minimal closed sets keep violating U as width grows.
- AbsorptionT t001 (every finite right half driven by 001 enters t001) is open. The evidence is computational only: 18,258 of 18,258 runs enter, with delays up to about 2*10^5. Adversarial strip inputs can avoid any fixed-width trap (round-2 barrier), so a proof would have to use that the right half is finitely supported.
- Minimality of t001 (width 47) is not established. Closures of its projections to widths 38..46 exceed 20,000 states. The C analysis rules out traps of width ≤ 22, so widths 23..46 are unresolved.
- No trap is known for 011, and no right-side mechanism was found. C3w 011 is the only route found, and it is open.
- Q001, C3s001 and C3w 011 are open. The death-time searches are finite evidence only (W ≤ 37 / 70 / 70).
- The final combination '(AbsorptionT t001 or Q001 or C3s001) together with C3w 011 excludes least period 3' is not one Lean theorem. It follows immediately from the separate Lean theorems, since a least-period-3 tail is 001 or 011 from some later time; the rotation-to-word step was not formalized here.
- The Lean modules import each other via scratch oleans (module names P3Ether etc.). Integration into ruliology-lean/Ruliology needs renaming; I did not touch the catalog.
- Empirical periodicity detection for 011 is heuristic: only periods up to about 2,500 steps (about 12,500 for small supports) within the horizons can be detected.

## Unconditional progress on Problem 1

None. Nothing here excludes least period 3, or any other period, unconditionally; as expected. The unconditional (Lean-checked) results are structural:
- the 12x3 ether and all its alignments;
- no ether wall of width 12 or less;
- the kernel-checked period-21 trap t001 for 001: entering it is contradictory, and it is provably reached by the empty right half;
- eventual forced skeletons (column 1 white at phase 0 under 001; black/white at phases 1/2 under 011);
- reductions of 001 to Q001 or C3s001 and of 011 to C3w 011.

Excluding least period 3 still requires one of the open statements for 001 (AbsorptionT t001, Q001 or C3s001) together with C3w 011.

# Adversarial verification

VERDICT: every Lean claim checks out, and every main computational claim reproduces exactly with independent code. Only two prose overstatements and one sub-claim I could not verify, all listed above. Nothing unconditional about period 3 follows, as the worker says.

Notes file: I did not write verify/VERDICT.md. The harness forbids report or findings .md files from subagents, and this structured output is what the script reads. Everything that file would hold is here.

Verification artifacts are in /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/p3-ether/verify/:
- vmk.sh
- src/ (byte-identical copies of the six modules) and build/ (my own oleans)
- ax/*_ax.lean (axiom prints)
- stmt/StmtCheck.lean (my restatements), plus StmtNeg.lean, CertNeg.lean and CertNeg2.lean (negative controls)
- comp/ (independent programs and their outputs)

LEAN
- All six modules compile from source, one process at a time, with `timeout 60 lake env lean` under the 4.30 toolchain.
  - Times and memory match the worker's: P3Ether 1.11 s / 0.60 GB, P3NoWall 8.84 s / 1.19 GB, P3Trap001 1.04 s / 0.63 GB, P3Reach 0.38 s, P3Left 0.78 s, P3Skel 0.45 s.
  - No errors or warnings. Olean sizes match the worker's byte-for-byte.
  - I built only against my own oleans, never the worker's lean/build. The catalog is up to date (`lake build --no-build` reports all targets current).
  - No file under ruliology-lean/Ruliology or the read-only Ruliology data dir is newer than the task file.
- `#print axioms` for all 24 listed theorems and their helpers gives only propext, Quot.sound and, for the skeleton results, Classical.choice.
- A grep of all six files finds no sorry, admit, native_decide, axiom, implemented_by, extern, unsafe, opaque, skipKernelTC, ofReduceBool, set_option, macro, notation, instance or attribute. The single hit is the word 'admits' in a docstring.
- StmtCheck.lean restates every claim in my own words with the definitions unfolded:
  - rule = xor l (c || r); cell; drv; L;
  - the ether table; aligned3; WallOK; EncF; PTrap.check/nodeOK/edgeOK;
  - AbsorptionT, Q001, C3w w011, C3s001; colPattern3 and effWord3.
  Lean accepts all of them, and negative controls are rejected.
- Corrupted certificates evaluate to false and fail: t001 with u bit 0 set, one bit of R flipped, or m = 42; the no-wall certificate with a zeroed distance entry.

COMPUTATIONS (my own code, independent of the worker's)
- Ether: confirmed to be a rule-30 orbit with the glide and the 6+6 alignments, and unique up to rotation.
- Walls: a greatest-fixed-point search finds the maximal closed set with the U-property empty for all 12 columns at width 16, and for columns 0–3 at widths 23, 24, 25 and 28. By the Lean-proved glide and lifting lemmas there is no wall at any width ≤ 28. The program is validated on the period-4 ether (wall exactly from width 13 at column 2).
- t001: my own decoder confirms closure, the U-property, the 38-column period-21 core, that it is not the ether, and that it is strongly connected. It is exactly the width-47 closure of a reachable state.
- Entry into t001 for 001, exact simulation with no truncation:
  - All 12,288 runs with support ⊆ [1,12] enter. Cumulative counts by 4,096 / 8,192 / 16,384 / 32,768 / 40,000 / 120,000 / 300,000 steps are 1418 / 3038 / 6216 / 9424 / 10296 / 12225 / 12288, which is 11.5 / 24.7 / 50.6 / 76.7 / 83.8 / 99.49 / 100%, identical to the worker. Maximum delay is 186,490 (x = 467, phase 0).
  - All 5,970 true right halves enter. 84.7% enter within 40,000 steps, and the maximum delay is 201,756 (T = 185, phase 2). My simulated center column matches center-1e7.bin with 0 mismatches for t ≤ 100,000.
  - Random width-64 halves: 84.0% enter within 40,000 (worker 83.6%).
- 011: column 1 is never periodic, in 12,288 small-support runs, 5,970 true halves, 900 random halves and 48 runs at horizon 100,000. The periodicity detector was positive-controlled: on 001 runs it finds period 14 samples (21 steps).
- Death-time tables: my brute force over all 2^W starts matches the worker's DFS exactly for Q001, C3s001 and C3w 011, all 3 phases, W = 1..28 (252 rows), with no survivors. Their headline values at W = 37 and W = 70 (94, 103, 99) reproduce, with identical node counts, when I compile their ldfs.c from source.
- Strip-graph SCCs: for both 001 and 011, every width 1–22 has a unique terminal SCC and it is BAD. This is cross-checked by brute-force reachability at widths 6 and 8, and positive-controlled on 0001 (GOOD, 109 states at width 16) and 0111 (GOOD, 188 states at width 14). So no labelled trap of width ≤ 22 exists.

GAPS AND HONESTY
- The worker states its gaps correctly:
  - AbsorptionT t001, Q001, C3s001 and C3w 011 are open;
  - the ether-and-wall theorems are framework results that are vacuous for every wall checked (none up to width 28);
  - the minimality of t001 is unknown;
  - the step 'least period 3 means a tail of 001 or 011 up to rotation' is not formalized (it is easy).
- REPORT.md was not written. The worker attributes this to the harness rule, and all content is in its structured output.
- Not independently checked (descriptive only): the 'temporary black-ended stripe' wording.
- No processes are left running, and none of the worker's files were modified.

## Refuted or unverified claims

- Summary item 2, as worded without a width bound: 'However, no wall exists' and 'So the period-3 ether-and-wall family is empty'. This holds only for widths ≤ 12 (Lean) and ≤ 28 (exhaustive search in this verification). Walls lift to wider strips, so absence at small widths says nothing about larger ones. The worker's own gaps section says 'Whether a wall exists at width > 28 is open'. The bounded versions are confirmed.
- Computational result 'the all-input closure of the observed 001 state ... has more than 5*10^6 states for b ≤ 46'. This is literally false. For b ≤ 20 the whole state space is 3·2^b ≤ 3,145,728. Recomputing from the worker's own seed (c(0)=1 then 001, T0 = 3000) gives 218 at b = 8, 1,634 at b = 12, 50,006 at b = 20 and 4,546,523 at b = 30. It does exceed 5·10^6 at b = 38, 44 and 46. The figures 815 at b = 47 and 1363..9590 at b = 48..52 are confirmed exactly. Minor wording error; no conclusion depends on it.
- UNVERIFIED, so counted as refuted under the uncertainty rule though not shown false: 'At each of these widths [up to 28] the strip relaxation has a unique minimal closed set, and it violates the U-property.' I confirmed uniqueness and the U-violation only for widths ≤ 22, at all four attachment columns. The worker's own probe for widths 24–28 (c/wall3b.c) does not establish uniqueness. The conclusion it supports, no wall up to width 28, is independently confirmed by my exhaustive search.

## Per-theorem checks (compiles / axioms ok / no sorry or tricks / statement matches)

- `Ruliology.CellularAutomata.Rule30EtherThree.ether3_rule` — yes / yes / yes / yes. Rebuilt from a byte-identical copy into my own verify/build: 1.11 s, 0.60 GB, no errors or warnings. Axioms are [propext, Quot.sound]. My restatement in verify/stmt/StmtCheck.lean is accepted by Lean: ether3Table equals the claimed columns 001 001 011 110 010 010 110 101 100 100 101 011 (rfl), and rule a b c = xor a (b || c) (rfl), so this is rule 30. An independent Python check confirms the orbit, and also that this (12,3) ether is unique up to rotation and time shift.
- `Ruliology.CellularAutomata.Rule30EtherThree.ether3_glide` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. The statement is ether3 (j+4) φ = ether3 j (φ+1). Python confirms it independently.
- `Ruliology.CellularAutomata.Rule30EtherThree.alignments_001_complete` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]; the six aligned3_001_* lemmas use [propext]. Lean accepts my restatement with the explicit list [(0,0),(1,0),(4,2),(5,2),(8,1),(9,1)] and aligned3 unfolded (∀ψ<3, ether3 j0 (ψ+s) = w[ψ]). A negative control with one pair dropped is rejected. Python gives the same six pairs.
- `Ruliology.CellularAutomata.Rule30EtherThree.alignments_011_complete` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. My explicit-list restatement [(2,0),(3,2),(6,2),(7,1),(10,1),(11,0)] is accepted, and Python agrees.
- `Ruliology.CellularAutomata.Rule30EtherThree.trap_invariant3` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. My fully unfolded restatement is accepted. WallOK is exactly (states r < 2^b) ∧ (U-property at the white phases of ether column a) ∧ (closure under both z via the catalog's stripStep, whose rule-30 semantics are proved in the catalog by testBit_stripStep). This is a correct framework theorem, but it is vacuous for every wall that exists: none of width ≤ 12 (Lean) or ≤ 28 (my exhaustive search). The worker says so.
- `Ruliology.CellularAutomata.Rule30EtherThree.ether_wall_trap3` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. It uses the catalog's Rule30MaskedJen.masked_jen with P = 3, and the k = 0 case is handled. Same vacuity caveat as trap_invariant3.
- `Ruliology.CellularAutomata.Rule30EtherThree.absorption3_excludes` — yes / yes / yes / yes. Axioms are [propext, Quot.sound], and the same holds for not_eventually_001/011_of_absorption3. My restatement, with Absorption3 and InFamily3 unfolded, is accepted. Because WallOK forces W to be empty for b ≤ 12 (Lean) and, by my search, for b ≤ 28, Absorption3 is false there and the implication is vacuous. The worker discloses this.
- `Ruliology.CellularAutomata.Rule30EtherThree.no_wall_le_12` — yes / yes / yes / yes. Build: 8.84 s, 1.19 GB. Axioms are [propext, Quot.sound]; nwCheck_0..3 use [propext]. Zeroing one distance entry of the certificate makes it evaluate to false and fail. The proof is sound: wallOK_lift, wallOK_back (glide), wallOK_mod, and nw_sound by induction on the distance. My independent greatest-fixed-point C search finds no wall up to width 28 for columns 0–3, which by the glide and lifting lemmas covers every column. It reproduces the period-4 wall exactly from width 13 at column 2 (1915 states, nothing at 11–12 or other columns).
- `Ruliology.CellularAutomata.Rule30EtherThree.t001_check` — yes / yes / yes / yes. decide +kernel; axioms are [propext]. Three negative controls all fail: setting u bit 0, flipping one bit of R, and changing m to 42. My own decoder, parsing the Lean literals directly, confirms: 815 distinct (strip, label) pairs; closure under both inputs checked as a set property with my own step function; column 1 at the white phases equals u(label) with u bits {1, 19}; columns 1..38 are a function of the label, each with least period 21; 0 of 38 core columns match any ether column; and the trap is strongly connected.
- `Ruliology.CellularAutomata.Rule30EtherThree.PTrap.trap` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. I checked check, nodeOK and edgeOK by rfl against my reading. The argument is sound: the invariant keeps the label advancing mod m, column 1 at white times equals u(label), so it is m-periodic, and masked Jen with P = m (m % 3 = 0) gives the contradiction.
- `Ruliology.CellularAutomata.Rule30EtherThree.trap_001` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. My restatement, with w = [false,false,true], b = 47, n = 815 and EncF unfolded, is accepted.
- `Ruliology.CellularAutomata.Rule30EtherThree.absorptionT_excludes` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. It uses the true right half at T (finite support via cell_eq_false_of_gt) and the catalog's cell_eq_drv, at phase 0.
- `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_absorption` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. My restatement with AbsorptionT t001 unfolded (∀ finite x, ∀ φ, ∃ t1 i, phase match ∧ EncF drv ...) is accepted by Iff.rfl. AbsorptionT is open; it is supported by the empirics I replicated, but those are not a proof.
- `Ruliology.CellularAutomata.Rule30EtherThree.t001_reached` — yes / yes / yes / yes. Build: 0.38 s. Axioms are [propext, Quot.sound]; rowN_empty_eq uses [propext]. stepN and rowN are exact (no truncation), and rowN_eq_drv links them to the catalog's drv. My independent simulation finds the empty half at phase 0 first enters t001 at exactly t = 1270.
- `Ruliology.CellularAutomata.Rule30EtherThree.col_m1_001` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. Hand derivation agrees: col -1 = c(t+1) xor (c(t) || col1), which gives (col1, !col1, 1) at phases 0, 1, 2. Restated and accepted.
- `Ruliology.CellularAutomata.Rule30EtherThree.col_m1_011` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. Hand derivation gives (!col1, 0, 1), which matches. Restated and accepted.
- `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_Q001` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. Q001 unfolds by Iff.rfl to exactly the claimed form, with L the catalog's driven left half (L_succ, L_zero, L_col0 restated). The proof starts at T' = T + 5, so m > 0 and the black phase falls at k = 0. Q001 is open.
- `Ruliology.CellularAutomata.Rule30EtherThree.Q001_stripe` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. stripe = decide (p % 2 = 1) (rfl). The stripe is infinite, so it is not a counterexample to Q001; it only shows that finiteness is needed, as claimed.
- `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_011_of_C3w` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. effWord3 w011 = [false,true,false] and colPattern3 w011 = [none, some false, some true] are checked, and C3w w011 unfolds by Iff.rfl to the claimed form. C3w 011 is open.
- `Ruliology.CellularAutomata.Rule30EtherThree.C3w_011_ether` — yes / yes / yes / yes. Axioms are [propext, Quot.sound]. etherLeft p = ether3 ((p+2)%12).toNat 0 is infinite, so it shows finiteness is needed and is not a counterexample.
- `Ruliology.CellularAutomata.Rule30EtherThree.skeleton_001` — yes / yes / yes / yes. Axioms are [propext, Classical.choice, Quot.sound], all allowed. It goes through the catalog's Cert.eventually_pred and Cert.sound_bad, with K001 checks by decide +kernel. My independent terminal-SCC computation agrees: at widths 4–22 only phase 0 is forced (white), and at width 3 nothing is forced.
- `Ruliology.CellularAutomata.Rule30EtherThree.skeleton_011` — yes / yes / yes / yes. Axioms are [propext, Classical.choice, Quot.sound]. My terminal-SCC analysis shows column 1 is {1} at phase 1, {0} at phase 2 and {0,1} at phase 0 at every width from 2 to 22, which agrees with the statement and with 'nothing more is forced'.
- `Ruliology.CellularAutomata.Rule30EtherThree.col_m1_001_skeleton` — yes / yes / yes / yes. Axioms are [propext, Classical.choice, Quot.sound]. It combines skeleton_001 with col_m1_001. Restated and accepted.
- `Ruliology.CellularAutomata.Rule30EtherThree.not_eventually_001_of_C3s` — yes / yes / yes / yes. Axioms are [propext, Classical.choice, Quot.sound]. C3s001 unfolds by Iff.rfl to fits3 [some false, none, some true] on the zero-boundary L. The claim that it is weaker than Q001 is right: a C3s001 counterexample, taken at a phase-2 time, is a Q001 counterexample. Open.
