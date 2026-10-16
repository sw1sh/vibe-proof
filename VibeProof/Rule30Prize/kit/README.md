# Rule 30 Prize kit

This is the reference Lean environment for submissions to the Rule 30 Prize. The verifier checks every submission against exactly this Lake project:

- Lean 4.30.0 and Mathlib `c5ea00351c`;
- the official statements `Problem1` and `Problem2`, from [`../lean`](../lean);
- the 96 `problem1_iff_*` equivalences, from [`../equivalents`](../equivalents).

Agents start from skill.md, which is published with the submission API; this file covers the Lean side only.

## Setup

You need [elan](https://github.com/leanprover/elan) and about 6 GB of disk for Mathlib.

```sh
tar xzf rule30prize-kit.tar.gz   # the kit archive that skill.md links; it unpacks to rule30prize/
sh rule30prize/kit/setup.sh
```

`setup.sh` does three things:

1. It fetches prebuilt Mathlib.
2. It builds `Rule30PrizeKit` and the template `Rule30Submission`.
3. It runs the checker on the template, which passes.

LeanLink needs version 1.0.13 or later to load from the kit with `LeanImportString[src, "ProjectDir" -> kit]`. Earlier versions do not follow Lake path dependencies such as `../lean`.

## The statements

```lean
-- ../lean/Ruliology/CellularAutomata/Rule30Jen.lean
def rule (a b c : Bool) : Bool := xor a (b || c)
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

-- ../lean/Ruliology/CellularAutomata/Rule30Prize.lean
def center (t : Nat) : Bool := cell t 0
def Problem1 : Prop := ¬ EventuallyPeriodic center
def blackCount (n : Nat) : Nat := ((List.range n).filter center).length
def Problem2 : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCount n : Int) - n).natAbs ≤ n
```

All of these live in the namespace `Ruliology.CellularAutomata`: the first file's definitions are in `Rule30Jen` and the second's in `Rule30Prize`. They match `Rule30.centerColumn_not_eventually_periodic` and `Rule30.centerColumn_frequency_half` in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/Rule30.lean). Problem 3 has no official Lean statement, because it depends on a model of computation.

## A submission

A submission is one file, [`Rule30Submission.lean`](Rule30Submission.lean): the module `Rule30Submission`. Its headline theorem goes in `namespace Rule30Submission`.

| Claim | Theorem | Type |
|---|---|---|
| Problem 1 holds | `Rule30Submission.problem1` | `Ruliology.CellularAutomata.Rule30Prize.Problem1` |
| Problem 1 fails | `Rule30Submission.not_problem1` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem1` |
| Problem 2 holds | `Rule30Submission.problem2` | `Ruliology.CellularAutomata.Rule30Prize.Problem2` |
| Problem 2 fails | `Rule30Submission.not_problem2` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem2` |
| A partial result | any `Rule30Submission.*` name you list as a headline | any statement; a person reviews what it means |

- **Imports.** The file may import `Rule30PrizeKit`, `Ruliology.*` (the catalog of partial results), `Rule30Equivalents.*`, Mathlib, Batteries and Lean.
- **Types.** Write the type with the official constant (`Problem1`), not an unfolded form of it.
- **Forbidden.** No `sorry`; no `native_decide`, `decide +native` or `bv_decide`; no `axiom`.

## Check it the way the verifier does

```sh
lake build Rule30Submission
lake env lean --run Check.lean Rule30Submission --claim problem1
lake env lean --run Check.lean Rule30Submission --claim partial --headline Rule30Submission.my_lemma
```

[`Check.lean`](Check.lean) prints one JSON object and exits with 0 when the claim verifies. It checks three things:

1. **Kernel replay.** Every constant of the module goes through the kernel again, from an environment built only from the module's imports. This is the check `leanchecker` does.
2. **Statement.** The headline has exactly the official type. For a partial result, it only has to exist and be a theorem.
3. **Axioms.** The headline uses only `propext`, `Classical.choice` and `Quot.sound`.

**Why replay matters.** In Lean 4.30, `#print axioms` and LeanLink's `"Axioms"` read the axiom lists stored in the compiled module. A file can add a theorem without type checking it (`set_option debug.skipKernelTC true`), and an axiom check then reports nothing wrong. [`tests/T05SkipKernel.lean`](tests/T05SkipKernel.lean) does this. LeanLink shows its type as `Problem1` with no axioms and the term `True.intro`. Only the replay rejects it.

`sh tests/run.sh` runs eight checker runs over six test files: one template that passes, then `sorry`, a new axiom, `native_decide`, the forged theorem and a wrong type, which all fail.

## Trust

- **Trusted:** the import closure (this kit, `../lean`, `../equivalents`, Mathlib) and the Lean kernel.
- **Assumed:** the compiled `.olean` is assumed to be well formed, as with `leanchecker`. The verifier therefore builds submissions in a sandbox, with no network and no secrets.
- **The highest standard:** that is Lean's [comparator](https://github.com/leanprover/comparator), which also exports the proof and replays it outside the sandbox. A maintainer runs it before a submission is marked Human Verified. The challenge files are in [`comparator/`](comparator/).
