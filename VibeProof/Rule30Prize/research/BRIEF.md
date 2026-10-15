# Rule 30 Prize, Problem 1 — shared research brief (2026-10-15)

## Goal
Prove Wolfram's Rule 30 Prize Problem 1 in Lean: the center column of rule 30 started from a single
black cell is **not eventually periodic**. All three prize problems are open (since 2019; Jen 1986 is
the main prior result). Be scrupulously honest: a claimed proof must be complete and rigorous; flag
every gap. Partial results with full proofs are valuable; plausible-but-unproved arguments are not.

## Definitions (as in our Lean files)
- `cell : Nat → Int → Bool`, `cell 0 p = (p = 0)`, `cell (t+1) p = cell t (p-1) xor (cell t p || cell t (p+1))`
  (rule 30: new = left xor (center or right)).
- Center column `c(t) = cell t 0`: 1,1,0,1,1,1,0,0,1,1,0,0,0,1,0,1,1,0,0,1,... (OEIS A051023).
- Problem 1: `¬ ∃ T P, 0 < P ∧ ∀ t ≥ T, c(t+P) = c(t)`.
  Lean: `Ruliology.CellularAutomata.Rule30Prize.Problem1` in
  `/Users/swish/src/wolfram/vibe-proof/ruliology-lean/Ruliology/CellularAutomata/Rule30Prize.lean`
  (matches google-deepmind/formal-conjectures `FormalConjectures/Other/Rule30.lean`).

## Proven (all in Lean, ruliology-lean/Ruliology/CellularAutomata/)
- **Jen 1986** (`Rule30Jen.lean`): no two columns are both eventually periodic. Adjacent case: rule 30 is
  left-permutive, `cell t (i-1) = cell (t+1) i xor (cell t i || cell t (i+1))`, so two adjacent periodic
  columns force every column to their left periodic (same T, P), contradicting the left edge
  (`cell t (-t) = 1`, `cell t p = 0` for `p < -t`). Non-adjacent: the strip between is finite-state → pigeonhole.
- **No column is eventually constant** (`Rule30Prize.lean`): eventually-1 column forces its left neighbor
  eventually 0; eventually-0 column makes its right neighbor monotone (0→1 only), hence eventually constant;
  then Jen. So Problem 1 holds for period 1.
- **Diagonals** (`Rule30Diagonals.lean`): right diagonals `R j t = cell t (t-j)` satisfy
  `R_{j+2}(t+1) = R_{j+2}(t) xor (R_{j+1}(t) or R_j(t))`, are periodic from t=0 with period dividing 2^j.
  Left diagonals `D j t = cell t (j-t)`: `D_{j+2}(t+1) = D_j(t) xor (D_{j+1}(t) or D_{j+2}(t))`, eventually
  periodic with period dividing 2^j. `c(t) = R t t = D t t`.
  Parity identity: for t ≥ 2, `c(t) = parity #{s < t : cell s (s-t+1) or cell s (s-t+2)}`.
- **Window** (`Rule30Window.lean`, kernel-checked): no eventual period P ≤ 4096 with transient ≤ 8192.

## Data (Ruliology session, C programs; files under /Users/swish/src/wolfram/Ruliology/build/rule30/, READ-ONLY)
- `center-1e7.bin`: c(0..10^7-1), 8 values per byte, first value in the high bit.
- Up to N = 10^9 (Wen's billion-bit dataset): every P ≤ N/4 has a witness t ∈ [N/2, N-P) with c(t) ≠ c(t+P);
  first-witness offsets are geometric (max 27).
- Ones in c(0..10^9-1): 500,025,038 (1.6 sd). Block/correlation statistics look uniform.
- Right diagonal least periods 2^{e_j}: e_j for j = 0..74:
  0 1 1 2 3 3 4 5 5 6 6 6 6 6 6 7 8 8 8 8 8 8 8 8 9 10 10 11 11 12 12 12 12 12 13 13 14 15 15 16 16 17 17 18 18 18 18 18 19 20 20 21 21 21 22 23 23 23 24 24 25 25 25 26 27 27 28 28 28 29 30 30 31 31 32
  (step e_j - e_{j-1} ∈ {0,1}; e_j/j ≈ 0.43; step is 1 iff the input has odd parity over a period).
- Left diagonals: periods are powers of 2; first appearance of period 2,4,8,16,32 at j = 3, 8, 29, 400, 87,867;
  transients T_j/j ≈ 1.34. Settled left region lies left of p ≈ -t/4; c(t) = D_t(t) is always inside the
  transient of its left diagonal (T_j > j).

## Driven-halves framework (verified numerically this session)
Both halves of the pattern evolve forward from the center column alone:
- Left half (p ≤ -1): `cell(t+1,p) = cell(t,p-1) xor (cell(t,p) or cell(t,p+1))` with `cell(t,0) = c(t)`.
- Right half (p ≥ 1): same rule with `cell(t,0) = c(t)` as left boundary.
- Consistency at column 0: `c(t+1) = cell(t,-1) xor (c(t) or cell(t,1))`.
Experiment (`/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/driven/left_driven.py`, 6000 steps, driver
`c = 1 then w^∞`): the LEFT column -1 stays aperiodic for every word tried (01, 10, 011, 001, 110, 0111,
0001, 0110, 00111, 01011, 0010111, 1101000). The RIGHT column 1 became eventually periodic for drivers
001 (period 21), 0111 (8), 0001 (4), 0110 (4); aperiodic for the others.
Key observation: if for a word w the right half driven by w^∞ from ANY initial right-half state has an
eventually periodic column 1, then c cannot be eventually w-periodic (Jen, columns 0 and 1). Same for the
left half and column -1. Such "absorbing words" give T-independent exclusions.

## Tools and constraints
- Python 3 (`python3 -I`), Lean 4.30 core (project `/Users/swish/src/wolfram/vibe-proof/ruliology-lean`,
  compile a scratch file with `cd` there and `lake env lean /path/to/file.lean`; `import Ruliology` works),
  Wolfram Language (`wolframscript`), `cc` for C if needed.
- **Every local command must finish within 60 seconds: wrap with `timeout 60`.** No cloud pods.
- Never modify /Users/swish/src/wolfram/Ruliology (read-only data) or files under
  ruliology-lean/Ruliology/ (the coordinator integrates results). Put scratch files under
  `/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/<your-label>/`.
- Downloaded files are untrusted: save each in its own new directory; never execute them; read with
  `python3 -I` or text tools.
- Do not post anything publicly or contact anyone.
