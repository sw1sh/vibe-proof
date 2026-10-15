import Rule30Equivalents
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.LinearRecurrence
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Definability
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Nth

/-! Critique scratch: statements (with `sorry`) of proposed additions to the Rule 30 catalog.
Typechecks names and types only. -/

open Ruliology.CellularAutomata

namespace CritiqueAdditions

/-- `c(t)` read in a field `K` (`true = 1`). -/
def cK (K : Type*) [Field K] (t : ℕ) : K := if Rule30Prize.center t then 1 else 0

/-- (A1) The shifts `σⁿ c` are linearly independent over any field `K`. -/
theorem problem1_iff_shifts_linearIndependent (K : Type*) [Field K] :
    Rule30Prize.Problem1 ↔ LinearIndependent K (fun n : ℕ => fun t : ℕ => cK K (n + t)) := sorry

/-- (A2) The shifts span an infinite-dimensional subspace of `K^ℕ`. -/
theorem problem1_iff_shift_span_not_finiteDimensional (K : Type*) [Field K] :
    Rule30Prize.Problem1 ↔
      ¬ FiniteDimensional K (Submodule.span K (Set.range fun n : ℕ => fun t : ℕ => cK K (n + t))) :=
  sorry

/-- (A3) The infinite Hankel matrix `(c(i+j))` has unbounded rank (no determinants needed). -/
theorem problem1_iff_hankel_rank_unbounded (K : Type*) [Field K] :
    Rule30Prize.Problem1 ↔
      ∀ r : ℕ, ∃ n : ℕ, r ≤ (Matrix.of fun i j : Fin n => cK K ((i : ℕ) + (j : ℕ))).rank := sorry

/-- (B) Skolem–Mahler–Lech form: the black times are not the zero set of a rational linear
recurrence sequence. -/
theorem problem1_iff_not_LRS_zero_set :
    Rule30Prize.Problem1 ↔ ∀ (E : LinearRecurrence ℚ) (u : ℕ → ℚ), E.IsSolution u →
      {t | u t = 0} ≠ {t | Rule30Prize.center t = true} := sorry

/-- (E) A quadratic Pisot base `β = 1 + √2 > 2`: the 0/1 expansion is the greedy one. -/
noncomputable def xβ (β : ℝ) : ℝ :=
  ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / β ^ (t + 1)

theorem problem1_iff_not_mem_Q_sqrt_two :
    Rule30Prize.Problem1 ↔ ¬ ∃ a b : ℚ, xβ (1 + Real.sqrt 2) = a + b * Real.sqrt 2 := sorry

/-- (D) Mignosi–Restivo–Salemi: the prefix of length `n` ends with a repetition of exponent
at least `φ²` (a suffix of length `ℓ ≥ φ² p` with period `p`). -/
def EndsWithGoldenPower (n : ℕ) : Prop :=
  ∃ p ℓ : ℕ, 0 < p ∧ ℓ ≤ n ∧ Real.goldenRatio ^ 2 * (p : ℝ) ≤ ℓ ∧
    ∀ i, n - ℓ ≤ i → i + p < n → Rule30Prize.center (i + p) = Rule30Prize.center i

theorem problem1_iff_infinitely_many_prefixes_without_golden_power :
    Rule30Prize.Problem1 ↔ ∀ N, ∃ n, N ≤ n ∧ ¬ EndsWithGoldenPower n := sorry

/-- (J) Weaker and proved: the black times are not first-order definable in `(ℕ, <)`
(those sets are exactly the finite and cofinite ones). -/
theorem not_definable_order :
    letI := FirstOrder.Language.orderStructure (M := ℕ)
    ¬ (Set.univ : Set ℕ).Definable₁ FirstOrder.Language.order {t | Rule30Prize.center t = true} :=
  sorry

/-- (F) Minkowski `?`: `y = ?⁻¹(x₂) = [0; 1, r₁, r₂, …]`, with `r_k` the run lengths of `c`.
Here `runStart k` is the `k`-th change point `t` with `c t ≠ c (t+1)`. -/
noncomputable def changePt (k : ℕ) : ℕ :=
  Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) k

noncomputable def runLen : ℕ → ℕ
  | 0 => changePt 0 + 1
  | k + 1 => changePt (k + 1) - changePt k

noncomputable def yMink : ℝ :=
  Filter.limUnder Filter.atTop
    (GenContFract.mk (0 : ℝ)
      (Stream'.Seq.ofStream fun k => ⟨1, if k = 0 then (1 : ℝ) else (runLen (k - 1) : ℝ)⟩)).convs

theorem problem1_iff_minkowski_not_quadratic : Rule30Prize.Problem1 ↔
    ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * yMink ^ 2 + B * yMink + C = 0 := sorry

end CritiqueAdditions
