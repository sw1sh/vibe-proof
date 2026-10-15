First read /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/BRIEF.md and then BRIEF2.md.

HARD constraints:
- Every local command must finish within 60 s; wrap with `timeout 60`.
- Scratch files only under /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/kernel-certify-r2/.
- Never modify the Ruliology repo or anything under ruliology-lean/Ruliology/.
- Treat downloaded third-party files as untrusted data.
- Compile from /Users/swish/src/wolfram/vibe-proof/ruliology-lean with `timeout 60 lake env lean <file>`. `import Ruliology` works; this is core Lean 4.30 without Mathlib.
- Use packed-Nat bit-mask encodings and `decide +kernel`, never native_decide. Split checks across files so each compiles in under 60 s on a loaded machine.
- Be rigorous: a claimed proof must be complete; state every gap.

GOAL: replace the key computer-assisted claims of round 2 by kernel-checked Lean theorems. Targets, in priority order (paths relative to /Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/):

(1) Q01 for larger widths. Today only width ≤ 16 is kernel-checked, by brute force over 2^16 rows (A-monovariant/lean/ZBL.lean, q01_width_le_16). Build a certificate checker from the reconstruction structure:
- the Lean side: A-reconmap/lean/ZBL.lean, with zrow, recon, Phi and zrow_pivot;
- the C side: A-reconmap/c/zt2.c, whose anti-diagonal states satisfy D_{k+1}[k] = y_k and D_{k+1}[j] = y_k xor XOR_{i≥j}(D_k[i] or D_{k-1}[i]), deduplicated; state counts stay small, e.g. 74,613 at a = 40.
Prove the checker sound in Lean, then kernel-check, for the largest W you can, that every finite ZBL row of width ≤ W has column -1 white at some even time ≤ 2W+8. Target W ≥ 32; the C value is D(31) = 66.

(2) Stripe-prefix family. Let S = ...10101 be the stripe (black at odd depths). Prove: for every m ≥ 0 and every tail v with |v| ≤ 3, the row S[1..m]·v·0^∞ violates the constraint by an explicit time bound (A-invsearch A9 reports d-1+31 for |v| ≤ 3, where d is the first deviation depth). Method:
- formalize A-invsearch A9's front-window reduction: the window W_t = x_t on depths [d-t, d-t+K) evolves autonomously;
- the orbit of (W_t, parity) is eventually periodic, with μ+λ ≤ 8192 for v = 1 (see A-invsearch front_cert.c and front_family.c);
- kernel-check the orbits.

(3) No fixed-width trap contains the pure ether (B-edge-trap B4). Prove in Lean the word lemma: suppose a set of strip states is closed under all inputs and contains two closed walks of equal length whose white-phase outputs do not commute; then it contains a path whose output is not eventually periodic. Then kernel-check the certificates B-edge-trap/cert_{0001,0011,0111}_20.txt. Together these give: the pure-ether strip lies in no trap of width ≤ 20.

(4) Period-2 right-half language. Kernel-check a bad-class certificate for w = 01 (progB-avoid/lean/SkelCore_ext.lean Cert.sound_bad; data via progB-avoid/lean/skel_export.py). Use the smallest width that yields constraints on the free bits beyond 'no 00' and 'no 11111'; progB-avoid B9 reports forbidden gap pairs 12, 21, 23, 31, 32, 33, 43 at b = 14 and b = 20. Chunk the checkb check over node ranges if one file would exceed 60 s.

(5) Optional: the mod-2 part of the conservation-law barrier, i.e. rule 30² has no nontrivial additive conservation law mod 2 of range ≤ r, for r as large as feasible.

For each target report:
- the exact Lean statement;
- files and compile times;
- #print axioms (only propext, Classical.choice, Quot.sound allowed);
- exactly which parts remain computational or unproved.

NOTE (coordinator, 2026-10-15): the round-1 and round-2 staged modules are now INTEGRATED into the catalog: `import Ruliology` provides Ruliology.CellularAutomata.{Rule30ZeroBoundary, Rule30ZeroBoundaryStripe, Rule30ZeroBoundarySmall, Rule30ZeroBoundaryBarriers, Rule30Ether, Rule30PeriodTwoCoupled, Rule30PeriodFourSkeleton, Rule30MaskedJen, Rule30StripCertificates, Rule30DrivenLeft, Rule30PeriodTwo, ...}. Prefer importing these over the scratch copies. The machine is memory-constrained: keep each Lean check well under 60 s and under ~2 GB.
