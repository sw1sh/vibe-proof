# Rule 30 Problem 1: equivalent forms

Rule 30 Prize Problem 1 asks whether the center column of rule 30, started from a single black cell, is ever eventually periodic. It is open. This folder collects statements that are **proved equivalent** to it in Lean 4 + Mathlib. A proof of any one of them is a proof of Problem 1.

```lean
-- the center column read as the binary number 0.c(0)c(1)c(2)…
noncomputable def centerBinary : ℝ := ∑' t, (if c t then 1 else 0) / 2 ^ (t + 1)

theorem problem1_iff_irrational_binary : Rule30Prize.Problem1 ↔ Irrational centerBinary
```

**Status:**
- 29 of the 53 equivalent forms in [CATALOG.md](CATALOG.md) are proved here, as 98 theorems named `problem1_iff_*`.
- Every one uses only `propext`, `Classical.choice` and `Quot.sound`. None uses `sorry` or `native_decide`.
- For each module, an independent verifier recompiled the file, checked its axioms and restated its main theorems.

## What is here

| Module | Problem 1 is equivalent to … | Headline theorems |
|---|---|---|
| [BinaryIrrational](Rule30Equivalents/BinaryIrrational.lean) | the irrationality of 0.c(0)c(1)… read in base 2, in base 10, or in any base B ≥ 2 | `problem1_iff_irrational_binary`, `problem1_iff_irrational_base` |
| [NumberTheory](Rule30Equivalents/NumberTheory.lean) | each of:<br>- the continued fraction of x₂ does not terminate;<br>- x₂ has infinitely many approximations with error below 1/q²;<br>- `LiouvilleWith 2 x₂`;<br>- x₂ has infinite order on the circle, and its multiples are dense there;<br>- x₂ is not preperiodic under doubling;<br>- no long division p/q produces the digits | `problem1_iff_cf_not_terminates`, `problem1_iff_dirichlet`, `problem1_iff_doubling_not_preperiodic`, `problem1_iff_not_rational_digits` |
| [TwoAdic](Rule30Equivalents/TwoAdic.lean) | the 2-adic number ∑ c(t) 2ᵗ is irrational; there is a congruence form for every base p ≥ 2; the 2-adic (FCSR) complexity is unbounded | `problem1_iff_padic_irrational`, `problem1_iff_padic_int`, `problem1_iff_two_adic_complexity` |
| [PowerSeriesF2](Rule30Equivalents/PowerSeriesF2.lean) | ∑ c(t) Xᵗ is not rational over F₂; no linear feedback shift register generates c; its linear complexity is unbounded | `problem1_iff_series_not_rational`, `problem1_iff_no_lfsr`, `problem1_iff_linear_complexity_unbounded` |
| [LinearRelations](Rule30Equivalents/LinearRelations.lean) | over any field: the series is not rational, and c solves no linear recurrence; the shifts of c are linearly independent; the Hankel rank is unbounded; Kronecker's determinant criterion holds over ℤ, F₂ and any field | `problem1_iff_shifts_linearIndependent`, `problem1_iff_hankel_rank_unbounded`, `problem1_iff_hankel_det_int` |
| [ShiftOrbit](Rule30Equivalents/ShiftOrbit.lean) | the shift orbit of c is infinite, and c is not preperiodic. Morse–Hedlund: c has at least n + 1 distinct blocks of every length n | `problem1_iff_infinite_shifts`, `problem1_iff_ncard_factors`, `problem1_iff_strictMono_ncard_factors` |
| [WordsAutomata](Rule30Equivalents/WordsAutomata.lean) | each of:<br>- no word repeats forever, and there is a right-special block of every length;<br>- the tail complexity is at least n + 1;<br>- the orbit closure and the ω-limit set are infinite;<br>- every finite-state predictor errs infinitely often, and no feedback shift register generates c | `problem1_iff_no_eventual_word`, `problem1_iff_right_special`, `problem1_iff_omegaLimit_infinite`, `problem1_iff_unpredictable` |
| [TransformsSeeds](Rule30Equivalents/TransformsSeeds.lean) | each of:<br>- the same for shifts of c, its XOR derivative, its running parity, and its decimations;<br>- the Π₂ form, and periods restricted to factorials;<br>- the formal-conjectures statement, and Wolfram's 2019 statement read as intended (the literal reading is degenerate);<br>- every stripe seed 1, 11, 101, 1011, … has exactly the center column c | `problem1_iff_xor_derivative`, `problem1_iff_decimation`, `problem1_iff_fc`, `problem1_iff_wolfram`, `problem1_iff_stripeSeed` |
| [IntegerRows](Rule30Equivalents/IntegerRows.lean) | the integer recurrence a(0) = 1, a(t+1) = a(t) XOR (2a(t) OR 4a(t)) (OEIS A110240): bit t of a(t) is not eventually periodic. Equivalently, the main diagonal of the bit array (j, t) ↦ bit j of a(t) is not eventually periodic, although every row j of that array is periodic with period dividing 2^j | `problem1_iff_integer_rows`, `problem1_iff_diagArray`, `diagArray_row_periodic` |
| [Symmetry](Rule30Equivalents/Symmetry.lean) | the same question for rule 86 (black seed), for rules 135 and 149 (white seed), and for the complemented column | `problem1_iff_rule86`, `problem1_iff_rule135`, `problem1_iff_rule149` |
| [Basic](Rule30Equivalents/Basic.lean) | — (shared definitions: the center column `c` and `EventuallyPeriodic`) | `problem1_iff_not_eventuallyPeriodic` |

Each module first proves a general theorem about every sequence `b : ℕ → Bool`, then specializes it to the center column. The general theorems hold for any 0/1 sequence. Some may be worth upstreaming to Mathlib, for example "`Real.ofDigits` is rational iff the digits are eventually periodic", Morse–Hedlund, `Irrational x → LiouvilleWith 2 x`, and Kronecker's Hankel criterion.

## Documents

- **[CATALOG.md](CATALOG.md)** covers all 53 known equivalent forms, grouped by field, with each one's statement, proof route, sources and Lean status. It also lists stronger statements (for example, transcendence or non-automaticity), weaker ones, related questions (Problems 2 and 3) and broader perspectives.
- **[TECHNIQUES.md](TECHNIQUES.md)** is a portfolio of recent (2024–2026) proof techniques that touch these forms, many of them AI-assisted and from other projects. Each technique carries its verification status, its transfer plan for rule 30 and its obstacle, and the file ends with a ranked shortlist of next experiments. Its summary is blunt: none of these techniques excludes any nonconstant eventual period.
- **[research/](research/)** holds the raw material: survey outputs, every verifier's report, and scratch statement and proof files (`research/scratch/`, not part of the build).

## Building

This is a Lake project on Lean 4.30.0. It pins Mathlib at commit `c5ea00351c` and depends on the core-Lean snapshot in [`../lean`](../lean) for `Rule30Prize.Problem1`.

```sh
cd VibeProof/Rule30Prize/equivalents
lake exe cache get        # prebuilt Mathlib
lake build                # about 1 minute; peak about 2.7 GB per module
lake env lean scripts/CheckAxioms.lean   # axioms of all problem1_iff_* theorems
```

## Adding an equivalent form

1. Pick an entry from [CATALOG.md](CATALOG.md) whose status is *Stated* or *Scratch proof*. Its suggested Lean statement is in the entry and in `research/scratch/`.
2. Prove a general theorem for every `b : ℕ → Bool`, then specialize it to `c` as `Rule30Prize.Problem1 ↔ X`.
3. Watch for:
   - double expansions in base 2;
   - eventually constant sequences (`Rule30Prize.center_not_eventually_constant` handles them for c);
   - `0 < P`.
4. Keep the file free of `sorry`, `native_decide` and new axioms. Add it to `Rule30Equivalents.lean`, and regenerate `scripts/CheckAxioms.lean`.
5. Have someone other than the author restate the main theorem from scratch and check that it says what it claims.

Next targets:
- port the scratch proofs for the Presburger, regular-language and realization forms;
- Engel or factorial-base expansions;
- automatic complexity;
- the Pisot base 1 + √2.

The hard classical ones are Fatou/Pólya–Carlson (natural boundary), Skolem–Mahler–Lech (zero sets over ℚ), Cobham–Christol, and the one-tape time gap.
