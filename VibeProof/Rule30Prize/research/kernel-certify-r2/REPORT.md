# kernel-certify-r2 — final batch report (2026-10-15)

> **Note (coordinator).** This file was written from the worker's and verifier's structured output, so lines saying REPORT.md or VERDICT.md "was not written" refer to the agents' own attempts. Paths under `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/` point at the scratch area this folder was copied from; the same files are under `VibeProof/Rule30Prize/research/`.


Written by the coordinator from the worker's structured output (the harness blocked subagent report files).

## Summary

Targets 1–4 are done and kernel-checked. The optional target 5 was not attempted. Everything was compiled by me with core Lean 4.30 against the integrated catalog, using `decide +kernel` only: no native_decide, no sorry, no new axioms (checked by grep over all four source trees). Every main theorem's #print axioms lists only items from {propext, Classical.choice, Quot.sound}. Problem 1 is not solved, and none of this excludes any eventual period.

REPORT.md was NOT written. The task asked for it, but the harness blocked the write ("Subagents should return findings as text, not write report files"). The full report is this structured output.

Sources live under /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/{t1,t2,t3,t4}/src/KC; module names do not clash, so the trees can be merged. Build each module from /Users/swish/src/wolfram/vibe-proof/ruliology-lean with:
`LEAN_PATH=<tN>/build timeout 60 lake env lean -j 1 -R <tN>/src -o <tN>/build/KC/X.olean <tN>/src/KC/X.lean`
`tN/build.sh` does this one process at a time and logs time and peak RSS to tN/logs. Use -j 1 for the chunk files: it keeps the peak at one chunk, about 1.5 GB. A parallel lake build of a 16-chunk file would exceed 2 GB.

(1) Q01 for every start of width ≤ 56 (asked: ≥ 32). `KC.Q01W56.q01_width_le_56`: every start of the catalog's ZBL supported at depths ≤ 56 has zrow x t 1 = false at some even t ≤ 100 = D(56). Also proved: the 2W+8 corollary, `not_inX_of_width_le_56` (¬ Rule30ZeroBoundary.InX x), and the W = 52 instance (bound 96).
- Method: I replaced the per-path, deduplicated DFS with a bit-sliced checker. A per-path DFS measures about 0.04 ms/node in the kernel, roughly 300 s at W = 40.
  - Anti-diagonals are listed by depth (`AD y k 0 k`). `R_{k+1} = y_k :: running-xor(R_k[i] or R_{k-1}[i-1])` (`scanN`).
  - Each natural number holds 2^18 lanes, one choice of the first 18 free bits per lane. The remaining free bits up to depth W are fixed per chunk.
  - Free bits after depth W are forced lanewise so that L(k+1) = 0; lanes die when L(k+1) = 1 at even levels.
- Soundness is fully proved in t1/src/KC/Q01Lanes.lean: `scanN_AD`/`level` (against `Rule30ZeroBoundary.recon` and `history_eq_recon`), `scanN_lin`, `pat_spec`, `run_sound`, `q01_of_checks`, `q01_of_chunks`.
- Data: 1024 chunk theorems `check 56 101 18 c = true` in 64 files of about 5.4 s and 1.5 GB each; 345 s in total. W = 52 uses 256 chunks, 80 s.

(2) Stripe-prefix family. `KC.StripeFront.stripe_prefix_family_list`: for every m and every v with |v| ≤ 3, rowV m v = S[1..m]·v·0^∞ has its first deviation from the stripe at some d ≤ m+5, and zrow is white at depth 1 at an even time ≤ d−1+31.
- Front-window reduction, proved in general: `stripe_below`, `win_step`/`testBit_fstep` (the window evolves autonomously), `win_orb`, and `sig_sound`. The post-arrival check is exact by the light cone, so a 32-cell window suffices. Also `seg`/`PathOK`/`Cycle`/`orb_mod`, then `front_sound` and `family_of_class`.
- The 16 classes (m mod 2, v) reduce to 8 purely periodic cycles: 4096 ×3, 16384 ×3, 65536 ×2 steps. The v = 1 cycle has length 4096 at K = 32.
- Kernel checks are 3 files, ≤ 2.8 s and ≤ 0.75 GB each.

(3) No trap of width ≤ 20 contains the pure ether.
- `stepW` is the catalog's strip step (lin3 (wordAt w φ :: s ++ [x])). `node_traj` proves the driven right half (Rule30Ether.drv/node) is a path of this relaxation. Trap := closed under all inputs, and along every path column 1 at white phases is eventually Q-periodic with 4 ∣ Q.
- `word_lemma`: a closed set containing a path to y, plus two closed walks at y of equal length L (4 ∣ L) whose column-1 outputs differ at a white offset, contains a path whose masked output is not eventually periodic. Blocks follow the powers of two.
- The certificates' non-commuting cycles c1, c2 give the equal-length walks c1c2 and c2c1. All 24 certificates in B-edge-trap/cert_{0001,0011,0111}_20.txt were converted to column-21 inputs and kernel-checked: 6 files, ≈5 s and ≤ 1.02 GB each.
- `stepW_take`/`escapes_take` lift any closed set of width 1 ≤ b < 20 to width 20.
- Result: `pure_ether_not_in_trap_{0001,0011,0111}`, for every alignment in A_w, every phase, and every width 1 ≤ b ≤ 20.

(4) Period-2 right half. Width b = 5 is the smallest width whose bad class forbids anything beyond 11/00000 in column 1, i.e. beyond no-00/no-11111 for the free bits. At b = 5 it forbids gap pairs 21 and 23. At b = 4 only the gap alphabet {1..4} holds; I checked pairs and triples.
- The catalog's `Rule30PeriodFourSkeleton.Cert.checkb`/`checkGb` are kernel-checked on a skel_export certificate (23 ranks, 42 bad nodes); no chunking was needed.
- New `PeriodTwoLang.occurs` (subset simulation over bitmasks) and `no_pattern` cover paths inside the bad class. With the catalog's `left_right_white` this gives `KC.PeriodTwoW5.free_bit_constraints`: if the center is (01)^∞ from T, the free bits (column −1 at white times) eventually never contain 00, 11111, 011010, or 01101110. Width 6 (`KC.PeriodTwoW6`) adds gap pair 12 and the triples 114, 132, 241, 243.

(5) Mod-2 conservation laws of rule 30²: not attempted.

## Lean theorems (compiled by the worker; re-verified independently)

### `KC.Q01W56.q01_width_le_56`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t1/src/KC/Q01W56.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 346.31 s

```lean
theorem q01_width_le_56 (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) : ∃ t, t ≤ 100 ∧ t % 2 = 0 ∧ Ruliology.CellularAutomata.Rule30ZeroBoundary.zrow x t 1 = false
```

Q01 for every zero-boundary-left-half start supported at depths ≤ 56: column −1 is white at some even time ≤ 100 (= D(56)). Uses 1024 kernel-checked chunk theorems `check 56 101 18 c = true` in t1/src/KC/Q01W56/C0..C63.lean (16 per file), plus the soundness theorem KC.Q01Lanes.q01_of_chunks.

### `KC.Q01W56.not_inX_of_width_le_56`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t1/src/KC/Q01W56.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 346.31 s

```lean
theorem not_inX_of_width_le_56 (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) : ¬ Ruliology.CellularAutomata.Rule30ZeroBoundary.InX x
```

No start of width ≤ 56 is constrained (column −1 black at all even times), i.e. the catalog's Q01 restricted to widths ≤ 56.

### `KC.Q01W56.q01_width_le_56_linear`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t1/src/KC/Q01W56.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 346.31 s

```lean
theorem q01_width_le_56_linear (x : Nat → Bool) (hx : ∀ k, 56 < k → x k = false) : ∃ t, t ≤ 2 * 56 + 8 ∧ t % 2 = 0 ∧ Rule30ZeroBoundary.zrow x t 1 = false
```

The requested form with the bound 2W+8 at W = 56.

### `KC.Q01W52.q01_width_le_52`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t1/src/KC/Q01W52.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 81.6 s

```lean
theorem q01_width_le_52 (x : Nat → Bool) (hx : ∀ k, 52 < k → x k = false) : ∃ t, t ≤ 96 ∧ t % 2 = 0 ∧ Rule30ZeroBoundary.zrow x t 1 = false
```

Q01 for widths ≤ 52 with the tight bound D(52) = 96. 256 chunks in 16 files of about 5 s each. Also built: q01_width_le_52_linear and not_inX_of_width_le_52, same axioms.

### `KC.Q01Lanes.q01_of_checks`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t1/src/KC/Q01Lanes.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 1.2 s

```lean
theorem q01_of_checks (W K n : Nat) (hn : n ≤ W / 2) (hc : ∀ c, c < 2 ^ (W / 2 - n) → check W K n c = true) (x : Nat → Bool) (hx : ∀ k, W < k → x k = false) : ∃ t, t < K ∧ t % 2 = 0 ∧ zrow x t 1 = false
```

Soundness of the bit-sliced anti-diagonal checker: if every chunk check passes, every start of width ≤ W dies at an even time < K. q01_of_chunks is the variant taking a ChunksOK range certificate; run_sound is the per-lane invariant (axioms [propext, Quot.sound]).

### `KC.StripeFront.stripe_prefix_family_list`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t2/src/KC/StripeFamily.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 8.63 s

```lean
theorem stripe_prefix_family_list (m : Nat) (v : List Bool) (hv : v.length ≤ 3) : ∃ d, 1 ≤ d ∧ d ≤ m + 5 ∧ (∀ k, 1 ≤ k → k < d → rowV m v k = stripe k) ∧ rowV m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (rowV m v) t 1 = false   -- rowV m v k := if k ≤ m then stripe k else v.getD (k - m - 1) false
```

For every m ≥ 0 and every tail |v| ≤ 3, the start S[1..m]·v·0^∞ deviates first from the stripe at some d ≤ m+5 and violates the Q01 constraint by time d−1+31. The companion stripe_prefix_family takes v as three Booleans.

### `KC.StripeFront.front_sound`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t2/src/KC/StripeFront.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 1.46 s

```lean
theorem front_sound (x : Nat → Bool) (d K S lam : Nat) (hd : 1 ≤ d) (hag : ∀ k, 1 ≤ k → k < d → x k = stripe k) (hSK : S + 1 ≤ K) (hcyc : Cycle K S (pk (fun i => x (d + i)) K) (d % 2) lam) : ∃ s, s ≤ S ∧ (d - 1 + s) % 2 = 0 ∧ zrow x (d - 1 + s) 1 = false
```

The front-window reduction (A9), proved in general: a checked periodic orbit of (window, front parity) bounds the death time of any start that is the stripe below its first deviation d. Built on win_step (autonomous window evolution) and win_orb.

### `KC.EtherTrap.word_lemma`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t3/src/KC/EtherTrap.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 0.94 s

```lean
theorem word_lemma (w : List Bool) (T : Nat × List Bool → Prop) (hT : Closed w T) (x0 y : Nat × List Bool) (hx0 : T x0) (hx04 : x0.1 < 4) (P : List Bool) (a b : Nat → Bool) (L j0 : Nat) (hP : traj w x0 (fun n => P.getD n false) P.length = y) (ha : traj w y a L = y) (hb : traj w y b L = y) (hL4 : L % 4 = 0) (hL0 : 0 < L) (hj0 : j0 < L) (hwhite : white w (traj w y a j0) = true) (hdiff : col1 (traj w y a j0) ≠ col1 (traj w y b j0)) : ∃ u, (∀ n, T (traj w x0 u n)) ∧ ¬ MaskedPer w (traj w x0 u)
```

Word lemma: a set of strip nodes closed under all inputs that reaches a node with two equal-length closed walks whose white-phase column-1 outputs differ contains a path whose white-phase output is not eventually periodic. Non-commuting cycles c1, c2 give the walks c1c2 and c2c1.

### `KC.EtherTrap.pure_ether_not_in_trap_0001`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t3/src/KC/EtherTrapMain.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 32.06 s

```lean
theorem pure_ether_not_in_trap_0001 (a : Nat × Nat) (ha : a ∈ A0001) (φ : Nat) (hφ : φ < 4) (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w0001 T) : ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b)
```

No trap (closed set on which column 1 at the white phases is eventually periodic along every path) of width 1..20 contains a pure-ether node of 0001, for every alignment and phase. Uses 8 kernel-checked certificates.

### `KC.EtherTrap.pure_ether_not_in_trap_0011`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t3/src/KC/EtherTrapMain.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 32.06 s

```lean
theorem pure_ether_not_in_trap_0011 (a : Nat × Nat) (ha : a ∈ A0011) (φ : Nat) (hφ : φ < 4) (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w0011 T) : ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b)
```

Same for 0011 (3 alignments × 4 phases = 12 certificates).

### `KC.EtherTrap.pure_ether_not_in_trap_0111`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t3/src/KC/EtherTrapMain.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 32.06 s

```lean
theorem pure_ether_not_in_trap_0111 (a : Nat × Nat) (ha : a ∈ A0111) (φ : Nat) (hφ : φ < 4) (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 20) (T : Nat × List Bool → Prop) (hT : Trap w0111 T) : ¬ T (φ, etherRow a.1 ((φ + a.2) % 4) b)
```

Same for 0111 (4 certificates). The pure_ether_escapes_* versions give the explicit escaping path inside any closed set.

### `KC.EtherTrap.node_traj`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t3/src/KC/EtherTrap.lean`
- axioms: [propext, Quot.sound]
- compile: 0.94 s

```lean
theorem node_traj (w : List Bool) (x : Nat → Bool) (b : Nat) : ∀ t, Rule30Ether.node w x t b = traj w (Rule30Ether.node w x 0 b) (fun t => Rule30Ether.drv (Rule30Ether.wordAt w) x t (b + 1)) t
```

The catalog's driven right half is a path of the strip relaxation stepW (input = column b+1), so the trap notion above is the one masked Jen uses.

### `KC.PeriodTwoW5.free_bit_constraints`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t4/src/KC/PeriodTwoW5.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 1.32 s

```lean
theorem free_bit_constraints (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = ((t - T) % 2 == 1)) : ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ col1Forbidden, ¬ ∀ i, i < pat.length → cell (t + 2 * i) (-1) = !pat.getD i false   -- col1Forbidden = [[1,1],[0,0,0,0,0],[1,0,0,1,0,1],[1,0,0,1,0,0,0,1]]
```

If the center column is (01)^∞ from T, then from some time on the free bits (column −1 at the white times) never contain 00, 11111, 011010 (gap pair 21) or 01101110 (gap pair 23). Width 5 is the smallest strip width giving constraints beyond 00/11111. col1_constraints is the same statement for column 1 (same axioms).

### `KC.PeriodTwoW6.free_bit_constraints`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t4/src/KC/PeriodTwoW6.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 2.31 s

```lean
theorem free_bit_constraints (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = ((t - T) % 2 == 1)) : ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ col1Forbidden, ¬ ∀ i, i < pat.length → cell (t + 2 * i) (-1) = !pat.getD i false
```

Width 6: nine forbidden column-1 words (11, 00000, gap pairs 21, 23, 12, gap triples 114, 132, 241, 243), complemented for the free bits.

### `KC.PeriodTwoLang.no_pattern`
- file: `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/t4/src/KC/PeriodTwoLang.lean`
- axioms: [propext, Classical.choice, Quot.sound]
- compile: 0.72 s

```lean
theorem no_pattern (C : Cert) (bad : Nat) (hw : C.w = [false, true]) (T T' : Nat) (hTT : T ≤ T') (h : ∀ t, T ≤ t → cell t 0 = C.wAt ((t - T) % C.P)) (hbad : ∀ t, T' ≤ t → C.rk ((t - T) % C.P) (rowR t C.b) = bad) (hb : 0 < C.b) (pat : List Bool) (hocc : occurs C bad pat = false) (t : Nat) (ht : T' ≤ t) (hph : (t - T) % 2 = 0) : ¬ ∀ i, i < pat.length → cell (t + 2 * i) 1 = pat.getD i false
```

Soundness of the subset-simulation language check on the bad class; combined with the catalog's Cert.sound_bad.

## Computational results

- Q01 node counts of the per-path anti-diagonal DFS (t1/nodes.c): W=32: 452,452; W=36: 1.84M; W=40: 7.35M. The deepest surviving depth equals the round-2 D(W) table for W = 1..42.
- Per-path kernel DFS cost was measured at about 0.04 ms/node with raw Nat primitives and Nat.rec/Bool.rec (W=28: 4.96 s, 1.19 GB). The bit-sliced lane checker does W = 40 in one chunk in 0.65 s. A per-path kernel run was abandoned as too slow.
- Python lane model (t1/lanes.py) passes with K = D(W)+1 levels and fails with K = D(W), for W = 11, 14, 20, 26 and 31. In the kernel, K = D(W) also fails (tested at W = 26 per-path and W = 40 lanes): the bounds are tight empirically, but tightness is not a theorem.
- Front-window orbits (t2/orbits.c, t2/certs.py): with K = 32 and the exact light-cone horizon 31, all 16 classes certify. Max post-arrival survival is 31 (attained). Orbits are purely periodic, with lengths 4096, 16384 and 65536. At K = 34 the lengths double, matching A9's 8192 for v = 1.
- B-edge-trap certificates: progB/B-edge-trap verify_cert.py re-run says all 8+12+4 certificates verified with pure-ether nodes covered. My converter t3/convert.py re-verifies the closed walks after converting to column-(b+1) inputs.
- Period-2 bad class for w = 01 (my reimplementation t4/badscc.py and t4/gaplang.py, subset simulation): b=3 has 14 nodes and nothing beyond 11; b=4 has 23 nodes and gap alphabet {1,2,3,4} only, with no forbidden gap pair or triple; b=5 has 42 nodes and forbidden gap pairs 21, 23; b=6 has 75 nodes and forbids 12, 21, 23 plus triples 114, 132, 241, 243; b=7 has 132 nodes and adds 131, 133. The existing files report b=14 (4015 nodes) forbidding 12, 21, 23, 31, 32, 33, 43; this was not re-run.

## Gaps

- REPORT.md was not written. The harness blocked the write: subagents must return findings as text, not write report files. The complete report is in this structured output; Lean sources, generators and build logs are in kernel-certify-r2/t1..t4.
- Target 1: Q01 itself is open. Widths 57..71 rest only on the C programs. The checker's cost doubles every +2 in W: W = 58 would be about 2048 chunks, about 14 min of sequential kernel time. That is feasible, but I stopped there because of the laptop compute limit. Tightness of D(W) is observed, not proved.
- Target 1 integration caveat: each chunk file (16 chunk theorems) peaks at about 1.5 GB only when theorems are checked sequentially (lean -j 1). A parallel lake build of such a file can exceed 2 GB, so split to fewer chunks per file or keep -j 1.
- Target 2: only tails |v| ≤ 3 are proved. A9's computational claim for |v| ≤ 7 (bound +45) is not kernel-checked; it needs windows ≥ 46 and much longer orbits.
- Target 3: covers widths 1..20 and the relaxation, where column b+1 is arbitrary. It says nothing about whether the true right half reaches the pure ether, and Absorption is still open. Width 0 is degenerate and excluded.
- Target 4: only b = 5 and b = 6 are kernel-checked. The stronger b = 14/20 constraints (gap pairs 31, 32, 33, 43) remain computational; b = 14 would need a chunked variant of the catalog's monolithic Cert.checkb. These constraints restrict the free bits but do not exclude period 2.
- Target 5 (optional, mod-2 conservation laws of rule 30²) was not attempted and remains computational (A-invsearch/conslaw*.py). Needed: a normal form h = h1 + c + δg, linearity of the conservation defect, vanishing of the defect for trivial laws on periodic configurations, and a kernel-checked left inverse of the defect matrix.

## Unconditional progress on Problem 1

None. Every result is a finite or family certificate for a reduction or barrier statement:
- Q01 restricted to widths ≤ 56.
- The stripe-prefix family with |v| ≤ 3.
- The absence of traps of width ≤ 20 containing the pure ether.
- Free-bit constraints under an assumed period 2.
None of them excludes an eventual period of the center column, period 2 included.

# Adversarial verification

All 15 listed theorems hold as stated: each compiles, uses only propext, Classical.choice and Quot.sound, contains none of the forbidden constructs, and says what the worker claims. The only refuted item is a side remark about build parallelism, which affects no theorem.

How I checked:
- I copied the worker's 109 source files into verify/src and appended #print axioms and #check lines to the 10 main files. The worker's files are unchanged.
- I rebuilt every dependency from source into my own build directory instead of trusting the worker's .olean files: 64 W56 chunk files, 16 W52 chunks, 3 stripe-cycle files, 6 trap-certificate files and all main files. I ran one Lean process at a time, each under timeout 60; the peak was 1.52 GB, about 8 minutes of kernel time in total.
- `lake build --no-build` confirmed the catalog modules used are up to date.
- A grep of all worker sources and the imported catalog modules found none of: sorry, admit, native_decide, axiom, implemented_by, extern, unsafe, opaque, skipKernelTC, ofReduceBool, set_option, or partial definitions.
- The definitions use rule 30 in the right orientation (new = left xor (center or right)): Rule30Jen.rule = xor a (b || c), zrow, lin3 and stepW. Every hypothesis is satisfiable, the quantifiers run the right way, and W, phase, alignments and b cover what is claimed.

Computational claims I reproduced:
- **D(W) table:** my own C brute force matches it for W ≤ 24. The kernel checker passes at K = D+1 and fails at K = D for W = 11, 12, 20, 26, 31 and 40. Since the checker is exact, this pins D(26)=44, D(31)=66 and D(40)=76.
- **Worker's DFS:** the worker's nodes.c, compiled and run by me, reproduces 452,452 / 1,840,438 / 7,354,717 nodes, and its deepest level equals the table for W = 1..42. lanes.py reproduces the pass/fail pattern at W = 11, 14 and 26. Calib3 takes 5.05 s and 1.19 GB, about 0.045 ms per node. A single-chunk W=40 check takes 0.72 s.
- **Stripe family:** my own window-orbit code reproduces the 8 cycles (4096, 16384, 65536), the class-to-cycle map, and a maximum survival of 31, which is attained. Direct simulation confirms it: no violation for m ≤ 1200, and exactly 31 at m = 4055–4057. At K = 34 the v=1 cycles have length 8192.
- **Trap certificates:** the round-2 verify_cert.py passes 8, 12 and 4 certificates, and the 24 lines map one-to-one onto the Lean certificates.
- **Period-2 bad class:** my own computation from the Lean definitions gives 14, 23, 42, 75 and 132 bad nodes for b = 3..7, the same forbidden pairs and triples, and the exact rank-0 sets of K5 (23 ranks) and K6 (54 ranks). An all-lengths check shows that b = 4 gives exactly {no 11, no 00000}, so b = 5 is the minimal width. This is stronger than the worker's pairs-and-triples check.

Caveats, all of which the worker states correctly:
- Problem 1 is not advanced, and no eventual period is excluded.
- Tightness of D(W) is empirical.
- Target 3 concerns the relaxation only; Absorption remains open.
- The period-2 constraints are conditional on the period-2 hypothesis.
- REPORT.md is missing.

VERDICT.md was not written: my subagent instructions forbid report files, so these notes are the verdict. Evidence is in /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/verify/: the build script vbuild.sh, logs/*.log with the axiom output, scripts/ (badclass.py, lang_full.py, dw_brute.c, stripe_direct.c, front_orbit.c), and the probe files src/KC/VTight.lean, VTight2.lean (the deliberate failure), VTight3.lean, VW40.lean and VPar.lean.

## Refuted or unverified claims

- Peripheral build note only; it affects no theorem. The claim: "Use -j 1 for the chunk files: it keeps the peak at one chunk, about 1.5 GB. A parallel lake build of a 16-chunk file would exceed 2 GB." My measurements contradict it for a single file. Chunk file C0 (16 theorems) peaks at 1.55 GB in 5.46 s with -j 2, the same as with -j 1. A 4-theorem test file has the same time (0.90-0.94 s) and peak (0.85-0.89 GB) with -j 1, -j 4, the default (16 CPUs) and -DElab.async=true. These decide +kernel checks run sequentially within a file, so -j 1 is not what bounds memory. The real hazard is building several chunk modules at once, about 1.5 GB each.

## Per-theorem checks (compiles / axioms ok / no sorry or tricks / statement matches)

- `KC.Q01W56.q01_width_le_56` — yes / yes / yes / yes. Rebuilt from source in my own build dir, without reusing the worker's oleans: Q01Lanes (1.31 s); all 64 chunk files C0..C63 (5.3-5.8 s and 1.48-1.52 GB each, about 349 s total, one process at a time); then the main file. #print axioms gives [propext, Classical.choice, Quot.sound]. Checked against the catalog definitions. zrow is rule 30 on depths >= 1 with a white wall: new depth k = depth k+1 xor (depth k or depth k-1), which is left xor (center or right) at position -k. zrow ignores x 0. The hypothesis means support in depths 1..56; the conclusion is a white depth-1 cell at some even time <= 100. The kernel types all_chunks : ChunksOK 56 101 18 0 1024, so the chunk ranges are contiguous and complete (2^(28-18) = 1024). 100 equals the round-2 D(56); tightness is not proved, as the worker says.
- `KC.Q01W56.not_inX_of_width_le_56` — yes / yes / yes / yes. Same build. Axioms [propext, Classical.choice, Quot.sound]. Proves ¬InX x, where InX x := ∀ s, zrow x (2s) 1 = true in the catalog, i.e. Q01 restricted to support in depths <= 56.
- `KC.Q01W56.q01_width_le_56_linear` — yes / yes / yes / yes. Same build. Axioms standard. This is the requested 2W+8 form (t <= 120), derived from the bound 100.
- `KC.Q01W52.q01_width_le_52` — yes / yes / yes / yes. 16 chunk files rebuilt (4.96-5.16 s and <= 1.49 GB each, about 81 s), then the main file (0.26 s). Axioms standard for q01_width_le_52, its _linear form and not_inX_of_width_le_52. The bound 96 equals the round-2 D(52).
- `KC.Q01Lanes.q01_of_checks` — yes / yes / yes / yes. 1.31 s, 0.48 GB. Axioms [propext, Classical.choice, Quot.sound]; run_sound, level and scanN_lin use only [propext, Quot.sound]. The proof is complete: the lane packs the first n free bits, the chunk packs the free bits y(2(n+s)+1) for s < W/2-n, and the width condition comes from history_eq_recon. The checker is exact: K = D(W)+1 passes and K = D(W) fails in the kernel at W = 11, 12, 20, 26, 31 and 40 (scratch files KC/VTight*.lean). This pins D(26)=44, D(31)=66 and D(40)=76, as in the round-2 table. My own C brute force (scripts/dw_brute.c) reproduces the table for W <= 24. A deliberately false claim (K = D(12)) was rejected, confirming the harness.
- `KC.StripeFront.stripe_prefix_family_list` — yes / yes / yes / yes. Rebuilt: StripeFront 1.54 s; StripeCycles0/1/2 at 2.18/1.53/2.91 s and <= 0.75 GB; StripeFamily 0.67 s. Axioms standard, including stripe_prefix_family. rowV m v k is stripe k for k <= m and v.getD (k-m-1) false after that; stripe k means k is odd, i.e. S = ...10101. Quantifiers: for all m and all v with |v| <= 3, there is a first deviation d <= m+5 and an even t <= d-1+31 with depth 1 white. Independent checks: (a) my own window-orbit code (scripts/front_orbit.c) reproduces the 8 cycles (4096 x3, 16384 x3, 65536 x2), the class-to-cycle map, and a maximum post-arrival survival of exactly 31, at orbit index 4057; at K=34 the v=1 cycles have length 8192. (b) Direct ZBL simulation without the window reduction (scripts/stripe_direct.c) finds no violation in any of the 16 classes for m <= 1200, and m = 4055/4056/4057 reach exactly 31, so the bound is attained.
- `KC.StripeFront.front_sound` — yes / yes / yes / yes. Axioms standard. Fully general: any x equal to the stripe at depths 1..d-1, with d >= 1, S+1 <= K, and a checked Cycle of (pk window, d % 2). win_step, win_orb and stripe_below are also proved; their axioms are standard and sig_sound uses only [propext, Quot.sound]. The worker's wording 'stripe below its first deviation' is slightly informal; the theorem only needs agreement with the stripe below d.
- `KC.EtherTrap.word_lemma` — yes / yes / yes / yes. EtherTrap.lean compiles in 0.98 s. Axioms standard. Hypotheses: Closed w T; T x0; phase < 4; an input word P from x0 to y; two closed walks a and b at y of equal length L with 4 | L and L > 0; a white offset j0 < L where column 1 differs. Conclusion: some path stays in T and has ¬MaskedPer. MaskedPer means eventual white-time periodicity with some Q > 0, 4 | Q. Requiring 4 | Q loses nothing, since a period of the masked column gives a multiple of 4, and it matches the use with masked Jen. The certificates use the walks c1c2 and c2c1 (from t3/convert.py).
- `KC.EtherTrap.pure_ether_not_in_trap_0001` — yes / yes / yes / yes. 6 certificate files rebuilt (4.76-5.47 s, <= 1.02 GB each) and the main file (0.38 s). Axioms standard; the escapes_* forms are standard too. stepW = lin3 (wordAt w φ :: s ++ [x]) is rule 30 on columns 1..b, with column 0 = w at phase φ and column b+1 = x. etherRow gives columns 1..b of the ether, with ether column j0 at ether phase φ+s. A0001 = [(5,0),(6,0)] is every alignment of 0001 in the 7-column ether. The theorem covers φ < 4 and 1 <= b <= 20, using escapes_take for b < 20. A Trap exists (the empty set), so the statement is not vacuous. Re-running the round-2 B-edge-trap/verify_cert.py verifies all 8 certificates. As the worker says, this concerns the relaxation, not the true right half.
- `KC.EtherTrap.pure_ether_not_in_trap_0011` — yes / yes / yes / yes. Same build and checks. A0011 = [(0,0),(1,3),(4,0)], which is complete. 12 certificates; the round-2 verify_cert.py re-run passes all 12.
- `KC.EtherTrap.pure_ether_not_in_trap_0111` — yes / yes / yes / yes. Same build and checks. A0111 = [(2,2)] (B3 = 1101 shifted by 2). 4 certificates; the verify_cert.py re-run passes all 4.
- `KC.EtherTrap.node_traj` — yes / yes / yes / yes. Axioms [propext, Quot.sound]. Shows that the catalog's Rule30Ether.node w x t b, built from drv (wordAt w) x, is traj of stepW with input column b+1, so the relaxation contains the true driven dynamics.
- `KC.PeriodTwoW5.free_bit_constraints` — yes / yes / yes / yes. PeriodTwoLang compiles in 0.74 s (unused-simp-argument linter warnings only); PeriodTwoW5 in 0.62 s. Axioms standard; col1_constraints is standard too. Uses Rule30Jen.cell, rule 30 from a single seed. The hypothesis is that the center is (01)^∞ from T, white at T+2k. The conclusion is that eventually, from no white time t do the free bits (column -1 at t, t+2, ...) spell 00, 11111, 011010 or 01101110. Independent recomputation (scripts/badclass.py, written from the Lean definitions): my b=5 bad class has 42 nodes and equals the rank-0 set of K5 exactly; K5 has 23 ranks, non-increasing on every edge. Minimality (scripts/lang_full.py, product of the subset and gap-shift automata, all word lengths): at b=4 the bad-class language under Lean's occurs semantics is exactly {no 11, no 00000}, and at b=3 only 11 is forbidden. So b=5 is the smallest width for this construction, which is stronger than the worker's pairs/triples check. The extra words at b=5 are exactly 100101 and 10010001.
- `KC.PeriodTwoW6.free_bit_constraints` — yes / yes / yes / yes. 1.66 s, 0.81 GB. Axioms standard. Nine words: 11, 00000, gap pairs 21, 23, 12 and gap triples 114, 132, 241, 243. Independently, the b=6 bad class has 75 nodes and equals K6's rank-0 set (54 ranks). My code reproduces the forbidden pairs 12/21/23 and triples 114/132/241/243, and at b=7 (132 nodes) it reproduces the additional 131 and 133.
- `KC.PeriodTwoLang.no_pattern` — yes / yes / yes / yes. Axioms standard. The statement matches: C.w = [false,true]; the center is C-periodic from T; the rank equals bad from T'; occurs C bad pat = false. Then from every white time t >= T', column 1 at t, t+2, ... does not spell pat. My independent implementation of occurs gives the same accept/reject results as all the kernel checks.
