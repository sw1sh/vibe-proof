# Deep dive: the row Ψ(∅)

**Goal.** Prove that Ψ(∅) has infinitely many black cells. Equivalently: no finite configuration supported on p ≤ 0, with every cell p ≥ 1 white, keeps its center alternating 1, 0, 1, 0, … from time 0. This is the simplest open instance of CQ01, the coupled period-2 problem. CQ01 implies no eventual period 2 (`Rule30PeriodTwoCoupled.no_eventual_period_two_of_CQ01`).

## Setup

Rule 30: new(p) = old(p−1) ⊕ (old(p) ∨ old(p+1)).

- **Center.** It alternates: black at even times, white at odd times.
- **Right half.** White at time 0, then driven by the center. This gives column +1 at all times.
- **Column −1.** It is forced:
  - black at even times;
  - the complement of column +1 at odd times.
- **Deeper columns.** Each follows sideways by left-permutivity: X_{k+1}(t) = X_k(t+1) ⊕ (X_k(t) ∨ X_{k−1}(t)), where X_k is column −k.
- **The row.** Ψ(∅)(k) = X_k(0) is the only time-0 left row that keeps the center alternating forever.

## Experiments (2026-10-17)

### 1. Computation and validation ([psi.c](psi.c))

- **Reach.** Ψ(∅) is computed to depth 2^20 in 25 s.
- **Validation.** I truncated Ψ(∅) to width W, simulated rule 30 by brute force with independent code, and recorded when the center stops alternating. It stops exactly at the first black depth of Ψ(∅) beyond W, for every W tested (5, 10, 20, 40, 64, 100, 200, 300). This is the exact-death identity. It is now a theorem for every right half R and every width: `Rule30PeriodTwoSideways.truncation_death` in the kit, with `exact_death_center` for any left row.

First 64 cells: `1100011011000101000001100010001000011001111110010000111111111101`.

### 2. Statistics and structure ([structure.c](structure.c))

| Test | Result | Random sequence would give |
|---|---|---|
| Density of black cells | 0.5009 at depth 2^20 | 0.5 |
| Longest white run up to depth n | 12 (2^15), 19 (2^16), 20 (2^20) | about log₂ n |
| White-run lengths | matches the geometric law up to length 20 | geometric(1/2) |
| 2-kernel: distinct n ↦ Ψ(2^k n + r), length 40 | 2^k for every k ≤ 14 (all distinct) | 2^k |
| Linear complexity over GF(2) (Berlekamp–Massey) | n/2 exactly, to n = 32768 | n/2 |

The row is not 2-automatic (no small automaton generates it) and satisfies no linear recurrence. On these tests it cannot be told apart from coin flips.

### 3. The reconstruction map as Boolean formulas ([anf.c](anf.c))

**Free bits.** The free bits f_s are column −1 at the odd times 2s+1. In the coupled problem, f = ¬(column +1 at odd times).

**Columns 2–4 by hand.** These follow from the sideways rule:

- column 2 at times 2s and 2s+1: ¬f_s and ¬f_s;
- column 3: f_s at 2s and f_{s+1} at 2s+1;
- column 4: ¬f_{s+1} at 2s, and ¬(f_s ∨ f_{s+1}) at 2s+1, the first nonlinearity.

**Time-0 row.** It is triangular:
- depth 2j depends on f_0 … f_{j−1}, and is the first cell where f_{j−1} appears (the pivot);
- depth 2j+1 depends only on the same f_0 … f_{j−1}.

**Algebraic shape.** I computed each row cell's algebraic normal form exactly, for 16 free bits.
- The degree grows like k/2.
- The number of monomials roughly doubles every two depths: 25,809 of the 65,536 possible at depth 33, about 39%. A random Boolean function has about 50%.

So the formulas are dense and generic, with no sparse, low-degree or recursive structure.

### 4. Is the empty right half absorbed? ([ucheck.c](ucheck.c))

**Why it matters.** T175 (`Rule30ZeroBoundary.free_not_eventuallyPeriodic`) says the free bits of a finite constrained row are never eventually periodic. So if u(∅), column +1 at odd times, were eventually periodic, CQ01 at R = ∅ would follow at once.

**Result.** It is not. There is no period ≤ 8192 on the second half of 131,072 terms. The empty right half is never absorbed into a trap.

### 5. Correlations with single-seed objects ([corr.c](corr.c))

Ψ(∅) agrees with the single-seed center column, at every shift d ∈ [−64, 64], exactly as often as chance predicts: max |z| = 2.55 over 129 shifts. The same holds for the single-seed left and right rows at T = 2048, 4096, 8192 and 16384 (|z| < 2).

## Theory notes

**One candidate.** For R = ∅ there is exactly one possible counterexample: the row Ψ(∅) itself. By the exact-death identity, any finite left row that keeps the alternation must equal Ψ(∅). The kit's `Rule30PeriodTwoSideways` proves this for every R (`Psi_unique`, `CQ01_iff_Psi`) and states the R = ∅ case as `CQ01Empty`.

- So CQ01 at R = ∅ says that one explicit, computable 0/1 sequence is not eventually zero.
- Since Ψ(∅) has black cells near depth 2^20, a counterexample would need width ≥ about 10^6.
- R = ∅ is not special: two steps later the same configuration has right half 11 and the same phase.

**The cascade picture of a finite configuration.** Index left anti-diagonals by m = depth − time.

- B_m ≡ 1 at the edge, m = W, and B_m ≡ 0 beyond it.
- Each anti-diagonal is a one-bit-memory transducer driven by the two deeper ones: B_{m−1}(t+1) = B_{m+1}(t) ⊕ (B_m(t) ∨ B_{m−1}(t)). Information flows from the edge toward the wall.
- Anti-diagonals with m ≤ 0 are born at the wall. The constraint (black at even times; the complement of u at odd times) concerns only their birth values.
- Near the edge every anti-diagonal is eventually periodic with a 2-power period. But a birth value always lies in its anti-diagonal's transient. This is the single-seed fact T_j > j, restated.

**Jen-type arguments.** Jen's proof needs two adjacent eventually periodic columns with a common (T, P); the sideways recurrence then spreads them to the left edge.

- Under period 2, only the center is periodic.
- Column −1 is constant at black times and equals ¬u at white times.
- Masked Jen (column +1 at white times is not eventually periodic) is consistent with this. It gives no contradiction.

**Descent.** The class Z₀ of finite configurations whose center alternates from time 0 is closed under F² but not under preimages: a preimage's center at time −1 is free.

- Every finite configuration traces back, through its unique finite preimages, to a *primitive* one with no finite preimage. The single seed is primitive.
- So FinConf at period 2 is equivalent to: no primitive finite configuration has an eventually alternating center.
- Primitive configurations are most of all finite ones (heuristically about 3/4), so this is no real reduction.

**Removing the edge cell.** This flips column −1 at time W − 1 through the xor channel, so it never preserves the constraint.

## Where this leaves the problem

The three tests agree with the panel: Ψ(∅) behaves like a random sequence. Proving it has infinitely many 1s is a pseudorandomness statement about one explicit deterministic sequence.

What is known about the target:
- it is implied by Q01, which says no finite constrained left row exists at all;
- the lasso barrier rules out any finite certificate;
- the same structural facts hold for rules 90/150/210, so a proof must use rule 30's OR.

## Directions not yet tried

1. **Correlations with structured rule-30 objects.** Compare Ψ(∅) and u(∅) with the single-seed center column, the single-seed left and right halves, the diagonals and the ether. A strong correlation with anything structured would be a lever.
2. **The forward picture: two edges.** In a finite configuration with alternating center, the left edge feeds xor-information into the center at times W + 2s. Look for a quantity carried from the edges that the alternation cannot absorb forever.
3. **A descent argument.** Every image of a finite configuration has a unique finite preimage (solve leftward from the right edge). Look for a way to shrink a hypothetical counterexample. The obstacle: the preimage's center at time −1 is unconstrained.
4. **Q01 instead of CQ01.** Q01 is a statement about a single autonomous system, the zero-boundary left half. Its death time D(W) ≈ 2W + O(1) fits a random-constraint model. Look for any monotone quantity along the forced continuation.
