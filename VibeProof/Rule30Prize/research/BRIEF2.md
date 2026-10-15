# Rule 30 Problem 1 — round-2 brief (state after round 1, 2026-10-15)

Read BRIEF.md first (definitions, constraints: every local command < 60 s via `timeout 60`, scratch only under
/Users/swish/.claude/jobs/b8cd2926/tmp/r30prize/<your-label>/, never modify the Ruliology repo or
ruliology-lean/Ruliology/, downloaded files are untrusted data).

## Status
Problem 1 is open. Literature (round 1): all claimed solutions are invalid; Condrey (arXiv 2609.09431, Sept 2026)
settled period 1 for every nonzero finite configuration and states period 2 is the next open case; Kopra (TCS 2023)
generalizes Jen. Third-party repos (Patto1155/rule30-foundry, Berzai, ghywel/placego, cochon123, Dibujaron) contain
word-specific exclusions and SAT horizons; none excludes period 2. Downloads (untrusted) under r30prize/lit-oss/dl/.

## Barriers (proved)
- Rules 90, 150, 210 share left-permutivity, Jen, diagonal periodicity, odometer structure, yet have eventually
  constant single-seed centers: any proof must use rule 30's OR and the finiteness of the seed.
- Realization: for any right half R and any target column c there is exactly one left half giving center c.
- Left barrier: edge-structured left states at onset T correspond 1-1 to column -1 on [T, 2T-2]; left-only
  arguments must look past 2T-1. Bounded-window/strip arguments cannot exclude any period (Condrey; local-obstruction).
- Strip relaxations (column b+1 free) admit aperiodic column-1-at-white-times histories for every word of length 2..7.

## Proved in Lean (scratch, standard axioms, no sorry) — integrate later
- Masked Jen (newideas/lean/R30NewIdeasAll.lean; left-consistency/LeftConsistency.lean): if column i is eventually
  Q-periodic, column i+1 restricted to the white times of column i is not eventually Q-periodic.
- Effective boundary (smallperiods): cell(t,-1) || c(t) = cell(t,-1) || (c(t) && c(t+1)); the left half evolves as
  rule 30 on p <= -1 driven by c'(t) = c(t) && c(t+1).
- Nine-black shield (Lemma A): 9 consecutive black cells in column m force (cell m+1, cell m+2) = (0,1) next.
  Consequences: no eventual period word whose black runs all have length >= 9; Theorem B (absorb-right/lean/
  AbsorbRight.lean): no period block with a black run >= 9*ceil((|u|+9)/2) ("black run >= ~0.82P+8.2"); Theorem D;
  0^r 11 for r >= 10 (AbsorbWhite.lean).
- Strip-certificate soundness (newideas, Cert.sound) with kernel-checked word exclusions (01111111, 00000011,
  0^10 1, 000000000101, 0011111111); generalize-jen/Rule30JenWindow.lean (weakened Jen, doubling-window defects,
  finitary Jen, strip certificates).
- Driven-left Jen (left-consistency/DrivenLeft.lean, complexity/lean/Rule30LeftDriven.lean): the left half driven by
  any eventually periodic column from a nonzero left-finite start has NO eventually periodic column.
- Right-diagonal period theory (diagonal/lean/RightPeriods.lean): e_{j+1} = e_j + R_{j+1}(2^{e_j}), rows at 2^k,
  restart/continuity, bounds log2(j+2)-1 <= e_j <= (2j+1)/3, no three doublings in a row, odometer.
- Rule 135 / white seed (gf2-algebra/lean/Rule135Center.lean): the center from a single white cell on black is
  column -1 of the usual pattern delayed; so at least one of the two centers is not eventually periodic.
- Window: if c(t+P) = c(t) for t >= T then T + P >= 16359 (complexity, kernel-checked); >= 9,999,957 conditional on
  data.

## The two frontier programs
**Program A — period 2 (Q_01).** If c alternates from T, then c'(t) = c(t) && c(t+1) = 0 for t >= T, so the left half
is the autonomous "zero-boundary left half" (ZBL): rule 30 on p <= -1 with column 0 forced white, started from the
finite configuration at time T. Then column -1 must be black at every time t >= T with c(t) = 1, i.e. at every
other step (and, from the right half's one-step constraint, its zeros at the other steps are 4..10 steps apart).
Q_01: no finite left configuration evolving as ZBL keeps cell(t,-1) = 1 at every other step forever.
Q_01 implies "the center column is not eventually 2-periodic" (for every transient). Finiteness is essential:
the infinite stripe ...10101 satisfies the constraint forever. Evidence: exhaustive search (coordinator
period2/search2_free.py; smallperiods; newideas LOP) — for every left support width W <= 39 every constrained
history dies within ~1.25W-2W steps; the reconstruction map from the free bits f_s = cell(T+2s+1,-1) to the initial
row L(k) = cell(T,-k) is triangular with a pivot at every other depth. Survival behaves like a random-constraint
model, so a proof needs genuine structure.

**Program B — least period 4.** For w in {0001, 0011, 0111} (all phases) there are certified traps S_w (sets of
right-strip states, columns 1..b, closed under every input from column b+1) in which column 1 at the white phases is
periodic (newideas: 0001 b=16 109 states; 0011 b=16 188; 0111 b=14 188; smallperiods: k+8 strips). If the true right
half ever enters S_w after T, masked Jen gives a contradiction. Random finite right halves always enter; adversarial
strip inputs can avoid them forever (avoiding states grow ~1.87^b), so a proof must use that the true right half is
finitely supported with the rigid right edge (ones on p = t, right diagonals periodic with 2-power periods,
right-edge insensitivity). Proving trap entry for every finitely supported right half excludes least period 4.
