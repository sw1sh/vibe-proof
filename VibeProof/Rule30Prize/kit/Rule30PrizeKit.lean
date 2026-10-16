import Ruliology.CellularAutomata.Rule30Prize
import Rule30Equivalents

/-!
# Rule 30 Prize kit, version 1

The reference Lean environment for submissions to the Rule 30 Prize: Lean 4.30.0 and
Mathlib `c5ea00351c`, pinned by `lean-toolchain` and `lake-manifest.json`.

* **The statements.** `Ruliology.CellularAutomata.Rule30Prize.Problem1` and `Problem2`, in
  `../lean/Ruliology/CellularAutomata/Rule30Prize.lean`, with the rule-30 pattern `cell` from
  `Rule30Jen.lean`. They match `Rule30.centerColumn_not_eventually_periodic` and
  `Rule30.centerColumn_frequency_half` in google-deepmind/formal-conjectures. Problem 3 needs a model
  of computation and has no official Lean statement.
* **Equivalent forms.** `Rule30Equivalents` proves 96 theorems `problem1_iff_*`, for example
  `Rule30Equivalents.BinaryIrrational.problem1_iff_irrational_binary`: Problem 1 holds iff the binary
  number `0.c(0)c(1)c(2)…` is irrational. A proof of any of these right-hand sides proves Problem 1.
* **Partial results.** `import Ruliology` brings the whole catalog of 60 modules (periods 1 to 4,
  black runs, Jen's theorem, barriers). This root does not import it, because the catalog's
  certificate modules are slow to build; import the modules you need.

A submission is the single module `Rule30Submission` (file `Rule30Submission.lean`). Its headline
theorem sits in `namespace Rule30Submission` with an official name and type, listed in `Check.lean`,
for example `theorem problem1 : Ruliology.CellularAutomata.Rule30Prize.Problem1`.
-/
