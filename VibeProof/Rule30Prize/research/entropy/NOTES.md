# Topological entropy of rule 30: numerical evidence for log 2

The kit proves log 2 ≤ h_top(rule 30) ≤ log 3 (`Mixing.log_two_le_coverEntropy`,
`Mixing.coverEntropy_le_log_three`). The upper bound counts the words of two adjacent columns
(N, N + 1), which determine everything to their left by left permutivity. The column pairs are a
factor of rule 30, so h_top equals the growth rate of the realizable column-pair words exactly.

## Counts

`multiplicity.c` enumerates the configurations on cells −L … L + 1 and records the pair
(column 0, column 1) over times 0 … L (n = L + 1 steps). For each column-0 word it counts the
distinct column-1 words:

| L  | max partners | average partners |
|----|--------------|------------------|
| 10 | 30 | 18.86 |
| 11 | 36 | 21.94 |
| 12 | 42 | 25.34 |
| 13 | 49 | 29.09 |
| 14 | 56 | 33.23 |

The maximum grows about quadratically, so the column-pair words number about 2^n n², not 3^n.
The growth ratio of all pair words falls from 2.67 (L = 2) to 2.31 (L = 12).

`prefixes.c` fixes a column-0 word u of length 18 and counts the column-1 prefixes of each length
over all right halves. For the alternating word the counts at lengths 14, 16, 18 are 36, 49, 64.

## Structure seen so far

- Where u = 0, column 1 can only turn from 0 to 1 (v(t+1) = v(t) ∨ w(t)), so it ends with 0^a 1^b.
- Where column 1 is 1, its next value is forced: v(t+1) = ¬u(t).
- With p(t) the first black cell of the right half: for p ≥ 3 the next value is 1 if u = 1 and
  p − 1 otherwise; p = 2 stays 2 under u = 1 and becomes 1 under u = 0. The only freedom is when
  p = 1 and u = 1: the new first black cell J depends on the deeper configuration. Even
  min(J, zero run + 3) is not determined by the column-1 history, so the polynomial bound comes
  from a subtler correlation.
- In diagonal coordinates rule 30 is the T-function Φ(x) = x ⊕ (2x ∨ 4x); the initial right half
  is the low part of the 2-adic state, evolves autonomously by Φ, and feeds the input-driven upper
  part only through OR carries.

Proving h_top = log 2 is open. Wolfram's note to NKS p. 960 gives evidence that the spacetime
entropy of rule 30 is 1 bit.
