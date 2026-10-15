import Rule30Equivalents
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Field.ZMod

/-! Merged-catalog scratch file 3/3: power series, recurrences, Hankel determinants and
transcendence over function fields. -/

open Ruliology.CellularAutomata
open scoped RatFunc

namespace Catalog

/-- `C(X) = ∑ c(t) Xᵗ` over a field `K`. -/
noncomputable def series (K : Type*) [Field K] : PowerSeries K :=
  PowerSeries.mk fun t => if Rule30Prize.center t then (1 : K) else 0

theorem problem1_iff_series_not_rational_F2 : Rule30Prize.Problem1 ↔
    ¬ ∃ P Q : Polynomial (ZMod 2), Q ≠ 0 ∧
      (Q : PowerSeries (ZMod 2)) * Rule30Equivalents.PowerSeriesF2.series Rule30Prize.center =
        (P : PowerSeries (ZMod 2)) :=
  Rule30Equivalents.PowerSeriesF2.problem1_iff_series_not_rational

theorem problem1_iff_linear_complexity_unbounded : Rule30Prize.Problem1 ↔
    ∀ d : ℕ, ∃ n : ℕ, ¬ ∃ a : Fin d → ZMod 2, ∀ t, t + d < n →
      ((if Rule30Prize.center (t + d) then 1 else 0 : ZMod 2)) =
        ∑ i, a i * (if Rule30Prize.center (t + i) then 1 else 0) :=
  Rule30Equivalents.PowerSeriesF2.problem1_iff_linear_complexity_unbounded

theorem problem1_iff_series_not_rational (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ¬ ∃ P Q : Polynomial K, Q ≠ 0 ∧ (Q : PowerSeries K) * series K = (P : PowerSeries K) := sorry

theorem problem1_iff_no_linearRecurrence (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
    ∀ E : LinearRecurrence K,
      ¬ E.IsSolution (fun t => if Rule30Prize.center t then (1 : K) else 0) := sorry

/-- Hankel determinant `det (c(i + j))_{0 ≤ i, j < n}` over `R`. -/
def hankel (R : Type*) [CommRing R] (n : ℕ) : R :=
  (Matrix.of fun i j : Fin n =>
    if Rule30Prize.center ((i : ℕ) + (j : ℕ)) then (1 : R) else 0).det

theorem problem1_iff_hankel_int : Rule30Prize.Problem1 ↔ ∀ N, ∃ n, N ≤ n ∧ hankel ℤ n ≠ 0 := sorry

theorem problem1_iff_hankel_F2 : Rule30Prize.Problem1 ↔
    ∀ N, ∃ n, N ≤ n ∧ hankel (ZMod 2) n ≠ 0 := sorry

theorem problem1_iff_not_pRecursive : Rule30Prize.Problem1 ↔
    ¬ ∃ (d N : ℕ) (p : Fin (d + 1) → Polynomial ℤ), (∃ i, p i ≠ 0) ∧
      ∀ n, N ≤ n → ∑ i : Fin (d + 1),
        (p i).eval (n : ℤ) * (if Rule30Prize.center (n + i) then 1 else 0) = 0 := sorry

theorem problem1_iff_transcendental_Q : Rule30Prize.Problem1 ↔
    Transcendental (RatFunc ℚ) ((series ℚ : PowerSeries ℚ) : LaurentSeries ℚ) := sorry

theorem problem1_iff_transcendental_F2_or_F3 : Rule30Prize.Problem1 ↔
    Transcendental (RatFunc (ZMod 2)) ((series (ZMod 2) : PowerSeries (ZMod 2)) : LaurentSeries (ZMod 2)) ∨
    Transcendental (RatFunc (ZMod 3)) ((series (ZMod 3) : PowerSeries (ZMod 3)) : LaurentSeries (ZMod 3)) :=
  sorry

/-- Stronger than Problem 1 (Christol: equivalent to `c` not being 2-automatic). Open. -/
def TranscendentalF2 : Prop :=
  Transcendental (RatFunc (ZMod 2)) ((series (ZMod 2) : PowerSeries (ZMod 2)) : LaurentSeries (ZMod 2))

end Catalog
