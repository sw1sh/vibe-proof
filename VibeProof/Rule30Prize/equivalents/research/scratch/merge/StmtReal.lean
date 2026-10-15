import Rule30Equivalents
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Merged-catalog scratch file 2/3: real-number, continued-fraction, circle, `p`-adic and complex
statements. Library theorems are referenced with `:=`; the rest is `sorry`. -/

open Ruliology.CellularAutomata

namespace Catalog

/-- `x₂ = 0.c(0) c(1) c(2) …₂`, as in `Rule30Equivalents.BinaryIrrational.centerBinary`. -/
noncomputable abbrev x₂ : ℝ := ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1)

/-! ## C. Real numbers -/

theorem problem1_iff_irrational_binary : Rule30Prize.Problem1 ↔ Irrational x₂ :=
  Rule30Equivalents.BinaryIrrational.problem1_iff_irrational_binary

theorem problem1_iff_irrational_base {B : ℕ} (hB : 2 ≤ B) : Rule30Prize.Problem1 ↔
    Irrational (∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1)) :=
  Rule30Equivalents.BinaryIrrational.problem1_iff_irrational_base hB

theorem problem1_iff_irrational_ofDigits (b : ℕ) [NeZero b] (hb : 2 ≤ b) : Rule30Prize.Problem1 ↔
    Irrational (Real.ofDigits (b := b) fun t => if Rule30Prize.center t then 1 else 0) := sorry

theorem problem1_iff_irrational_cantorFunction (b : ℕ) (hb : 2 ≤ b) : Rule30Prize.Problem1 ↔
    Irrational (Cardinal.cantorFunction (1 / (b : ℝ)) Rule30Prize.center) := sorry

theorem problem1_iff_not_rational_digits : Rule30Prize.Problem1 ↔
    ¬ ∃ p q : ℕ, 0 < q ∧ ∀ t, Rule30Prize.center t = decide (2 ^ (t + 1) * p / q % 2 = 1) := sorry

theorem problem1_iff_cf_not_terminates : Rule30Prize.Problem1 ↔
    ¬ (GenContFract.of x₂).Terminates := sorry

theorem problem1_iff_dirichlet : Rule30Prize.Problem1 ↔
    {q : ℚ | |x₂ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := sorry

theorem problem1_iff_liouvilleWith_two : Rule30Prize.Problem1 ↔ LiouvilleWith 2 x₂ := sorry

theorem problem1_iff_infinite_order : Rule30Prize.Problem1 ↔
    ¬ IsOfFinAddOrder (x₂ : AddCircle (1 : ℝ)) := sorry

theorem problem1_iff_dense_multiples : Rule30Prize.Problem1 ↔
    DenseRange (· • (x₂ : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) := sorry

theorem problem1_iff_doubling_not_preperiodic : Rule30Prize.Problem1 ↔
    ∀ m, (fun y : AddCircle (1 : ℝ) => 2 • y)^[m] (x₂ : AddCircle (1 : ℝ)) ∉
      Function.periodicPts (fun y : AddCircle (1 : ℝ) => 2 • y) := sorry

/-- `θ = [1 + c(0); 1 + c(1), 1 + c(2), …]`, the limit of the convergents. -/
noncomputable def θ : ℝ :=
  Filter.limUnder Filter.atTop
    (GenContFract.mk (1 + if Rule30Prize.center 0 then (1 : ℝ) else 0)
      (Stream'.Seq.ofStream fun t =>
        ⟨1, 1 + if Rule30Prize.center (t + 1) then (1 : ℝ) else 0⟩)).convs

theorem problem1_iff_not_quadratic : Rule30Prize.Problem1 ↔
    ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * θ ^ 2 + B * θ + C = 0 := sorry

/-! ## D. `p`-adic numbers -/

/-- `α = ∑ c(t) 2ᵗ ∈ ℤ₂`. -/
noncomputable def α₂ : ℤ_[2] := ∑' t, (if Rule30Prize.center t then (1 : ℤ_[2]) else 0) * 2 ^ t

theorem problem1_iff_padic_irrational : Rule30Prize.Problem1 ↔ ∀ q : ℚ, (α₂ : ℚ_[2]) ≠ q := sorry

/-- Partial sums `∑_{t<n} c(t) pᵗ`. -/
def S (p n : ℕ) : ℤ := ∑ t ∈ Finset.range n, (if Rule30Prize.center t then 1 else 0) * (p : ℤ) ^ t

theorem problem1_iff_padic_int (p : ℕ) (hp : p.Prime) : Rule30Prize.Problem1 ↔
    ¬ ∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * S p n - a := sorry

theorem problem1_iff_two_adic_complexity : Rule30Prize.Problem1 ↔
    ∀ B : ℕ, ∃ n, ¬ ∃ a b : ℤ, b ≠ 0 ∧ |a| ≤ B ∧ |b| ≤ B ∧ (2 : ℤ) ^ n ∣ b * S 2 n - a := sorry

/-! ## E. Complex analysis -/

/-- `f(z) = ∑ c(t) zᵗ`. -/
noncomputable def genFun (z : ℂ) : ℂ := ∑' t, (if Rule30Prize.center t then (1 : ℂ) else 0) * z ^ t

theorem problem1_iff_natural_boundary : Rule30Prize.Problem1 ↔
    ∀ z₀ : ℂ, ‖z₀‖ = 1 → ∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball z₀ r) ∧
        ∀ z ∈ Metric.ball z₀ r, ‖z‖ < 1 → g z = genFun z := sorry

/-! ## Stronger statements (each implies Problem 1; all open) -/

def Transc : Prop := Transcendental ℚ x₂

def ExponentTwo : Prop := Irrational x₂ ∧ ∀ p > (2 : ℝ), ¬ LiouvilleWith p x₂

/-! ## Problem 2 forms -/

theorem problem2_iff_tendsto : Rule30Prize.Problem2 ↔
    Filter.Tendsto (fun n : ℕ => (Rule30Prize.blackCount n : ℝ) / n) Filter.atTop
      (nhds (1 / 2)) := sorry

theorem problem2_iff_abel : Rule30Prize.Problem2 ↔
    Filter.Tendsto (fun x : ℝ => (1 - x) * ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) * x ^ t)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / 2)) := sorry

end Catalog
