# Findings already established in this session (2026-10-10)

These are facts the coordinator checked directly before the scout began. The report should use them, and researchers may extend or correct them.

## Problem framing
- Hofstadter Q: Q(1)=Q(2)=1, Q(n)=Q(n−Q(n−1))+Q(n−Q(n−2)) for n>2. It is "defined for all n" iff every lookback index stays ≥ 1.
- Equivalent form: Q is total ⟺ Q(n) ≤ n for all n ≥ 1. Only the n−1 lookback can fail first: at step n the n−2 lookback is ≥ 2 because Q(n−2) ≤ n−2 was checked at step n−1.
- Wolfram's 2024 essay "Nestedly Recursive Functions" uses the convention f(n)=1 for n ≤ 0, which makes totality trivial. The interesting question needs Hofstadter's original setup, with no values at n ≤ 0.
- Status: open. OEIS A005185 says: "not even known if this sequence is defined for all positive n". Roman Pearce (2014) computed it to n ≤ 10^10 and M. Eric Carr (2023-07-02) to n ≤ 3·10^10. The sequence also appears as Guy UPINT E31 and as Erdős Problem #422 (attributed to Hofstadter, cited [ErGr80]; erdosproblems.com lists it as open and marks it formalized).

## Existing formal artifacts checked directly
- **Mathlib**: grepped a local checkout (commit c5ea00351c, 2026-05-26, Lean v4.30.0) for hofstadter, meta-fibonacci and golomb. No hits.
- **google-deepmind/formal-conjectures** `FormalConjectures/ErdosProblems/422.lean` (fetched raw from main, 2026-10-10):
  - Defines `IsHofstadterQ (f : ℕ+ → ℕ+) : Prop := f 1 = 1 ∧ f 2 = 1 ∧ ∀ n : ℕ+, 2 < n → f (n - 1) < n ∧ f (n - 2) < n ∧ f n = f (n - f (n - 1)) + f (n - f (n - 2))`.
  - Its docstring says "At most one function satisfies this predicate. Some function satisfies it iff f(n) is well-defined for all n, which is not known." The uniqueness claim is not proved in the file.
  - Test lemmas `erdos_422.test.f3` (f 3 = 2) and `erdos_422.test.f4` (f 4 = 3) are proved.
  - Four open statements, each of the form `answer(sorry) ↔ ∀ f, IsHofstadterQ f → …`: `erdos_422` (misses infinitely many integers), `.variants.surjective`, `.variants.growth_rate` (an `=O[atTop] answer(sorry)` form) and `.variants.eventually_const`.
  - GAP: no statement of well-definedness itself (`∃ f, IsHofstadterQ f`). Every stated question holds vacuously if Q dies, so each "answer" silently depends on totality.
- `gh search code Hofstadter --repo google-deepmind/formal-conjectures` returned only ErdosProblems/422.lean and ErdosProblems/423.lean. File 423 is a different "Hofstadter sequence", OEIS A005243 (a(1)=1, a(2)=2, sums of consecutive terms).

## Lean experiments run this session (Lean 4.30.0 core, no Mathlib; Mac with 48 GB RAM)
Files are preserved in `VibeProof/HofstadterQ/experiments/`.
- **Padded total definition** (`QDefinition.lean`). It compiles. `#eval` gives 0,1,1,2,3,3,4,5,5,6,6,6,8,8,8,10,9,10,11,11 for n=0..19, matching A005185 for n ≥ 1:
  `def q : Nat → Nat | 0 => 0 | 1 => 1 | 2 => 1 | n + 3 => q (n + 3 - max 1 (q (n + 2))) + q (n + 3 - max 1 (q (n + 1)))`, with `termination_by n => n` and `decreasing_by all_goals omega`.
  The same file also states the relational spec `IsQ` and the Prop `HofstadterQTotal := ∃ f, IsQ f`.
- **`native_decide`** (`QNativeDecide.lean`) uses an Array-based Bool checker run by the interpreter in a plain `lean` file. N=10^6 took 2.3 s wall and N=10^7 took 5.8 s, both including startup. This route trusts the compiler (`Lean.ofReduceBool`).
- **Kernel-only `decide +kernel`** (`QKernelDecide.lean`) uses a fuel-bounded binary trie with structural recursion, because WF-recursive definitions do not reduce in the kernel:

  | N | wall time | notes |
  |---|---|---|
  | 300 | 0.9 s | |
  | 1000 | 2.9 s | |
  | 3000 | 10.5 s | |
  | 10^4 | 53.7 s | 8.2 GB max RSS |
  | 5·10^4 | not finished | killed after ~11 min while swap thrashed (~19 of 20 GB used) |

  So the naive kernel route caps near 10^4. One untested idea for going further: give the table as a single big Nat literal and check the recurrence pointwise with GMP-accelerated shifts, so memory stays flat.
- In both routes the real formal work is the soundness lemma linking the checker to the spec, not running the check.

## Numerical sanity checks (Python, `experiments/sanity_checks.py`)
- **Conway's $10k sequence** a(n)=a(a(n−1))+a(n−a(n−1)), a(1)=a(2)=1. It is slow (increments 0 or 1) up to 10^6. The last n with |a(n)/n − 1/2| ≥ 1/20 is n=1489, consistent with Mallows. Totality is trivial: if 1 ≤ a(m) ≤ m for m < n, then both indices lie in [1, n−1] and a(n) ≤ a(n−1) + (n − a(n−1)) = n.
- **Hofstadter–Huber V**, V(1..4)=1 and V(n)=V(n−V(n−1))+V(n−V(n−4)). It is slow up to 10^6, consistent with Balamohan–Kuznetsov–Tanny, J. Integer Seq. 10 (2007), Art. 07.7.1. Allouche–Shallit (arXiv 1103.1133) show it is 2-automatic.
- **Golomb's initial conditions** Q(1..3)=3,2,1 with the Q recurrence give, for k ≥ 1, Q(3k+1)=3, Q(3k+2)=3k+2, Q(3k+3)=3k+1. Verified to 10^5.
- **Parity-perturbed Q**, Q(n)=Q(n−Q(n−1))+Q(n−Q(n−2))+(−1)^n with Q(1)=Q(2)=1, is defined to 10^6. First terms: 1,1,1,3,3,3,5,5,5,7,5,9,7,9,7.

## Recent literature already identified (to be verified and extended)
- **Mantovanelli, arXiv 2603.29622**, "Certified Return-Word Induction for a Perturbed Hofstadter Recursion".
  - Versions: v1 2026-03-31, v2 2026-05-18, v3 2026-07-22. 27 pp. math.CO and math.NT.
  - An earlier title, reported by emergentmind, was "A Finite-State Proof of the Well-Definedness of a Perturbed Hofstadter Sequence".
  - Proves the parity-perturbed Q is well-defined for all n ≥ 1, by computer-assisted return-word induction: 13 return-word types, 92 synchronized cursor states, 122 transition rules, and 8 infinite word families handled as 10 parameterized schemas, with lag bounds ≥ 38. Supplementary code and certificates are on Zenodo.
  - v3 replaced the earlier finite-state closure argument. The paper states the reduction "does not appear to extend to the unperturbed sequence".
- **Nathan Fox**:
  - arXiv 1611.08244, "A Slow Relative of Hofstadter's Q-Sequence" (2016): B(n)=B(n−B(n−1))+B(n−B(n−2))+B(n−B(n−3)) with a generalized initial condition; slow, with its frequency sequence fully described.
  - arXiv 1807.01365, "A New Approach to the Hofstadter Q-Recurrence" (2018).
  - A talk, "Hofstadter-like Sequences over Nonstandard Integers".
- Emergentmind page "Well-definedness of the classical Hofstadter Q-sequence" frames the open problem.
