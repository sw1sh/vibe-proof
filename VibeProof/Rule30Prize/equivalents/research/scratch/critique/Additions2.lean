import Rule30Equivalents
import Mathlib.Computability.DFA
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.LinearRecurrence
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.List.PeriodicityLemma
import Mathlib.NumberTheory.Dioph

/-! Critique scratch 2: more proposed statements (with `sorry`); names and types only. -/

open Ruliology.CellularAutomata

namespace CritiqueAdditions2

/-- (A9) `M` accepts `x` and no other word of the same length (Shallit–Wang). -/
def UniquelyAccepts {σ : Type} (M : DFA Bool σ) (x : List Bool) : Prop :=
  x ∈ M.accepts ∧ ∀ y : List Bool, y.length = x.length → y ∈ M.accepts → y = x

/-- Deterministic automatic complexity of `x` is at most `K`. -/
def AutComplexityLE (x : List Bool) (K : ℕ) : Prop :=
  ∃ M : DFA Bool (Fin K), UniquelyAccepts M x

theorem problem1_iff_automaticComplexity_tendsto_top : Rule30Prize.Problem1 ↔
    ∀ K : ℕ, ∀ᶠ n in Filter.atTop,
      ¬ AutComplexityLE ((List.range n).map Rule30Prize.center) K := sorry

/-- (A8) `w` has a border: a nonempty proper prefix that is also a suffix. -/
def Bordered (w : List Bool) : Prop :=
  ∃ k, 0 < k ∧ k < w.length ∧ w.take k = w.drop (w.length - k)

theorem problem1_iff_late_long_unbordered_factors : Rule30Prize.Problem1 ↔
    ∀ n L : ℕ, ∃ i ℓ : ℕ, n ≤ i ∧ L ≤ ℓ ∧
      ¬ Bordered ((List.range ℓ).map fun j => Rule30Prize.center (i + j)) := sorry

/-- (A11, stronger) `C(X) = ∑ c(t) Xᵗ` satisfies no algebraic differential equation over `ℚ`. -/
noncomputable def C : PowerSeries ℚ :=
  PowerSeries.mk fun t => if Rule30Prize.center t then (1 : ℚ) else 0

def Hypertranscendental : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℚ), P ≠ 0 →
    MvPolynomial.aeval (fun i : Fin (n + 2) =>
      if (i : ℕ) = 0 then (PowerSeries.X : PowerSeries ℚ)
      else (⇑(PowerSeries.derivative ℚ))^[(i : ℕ) - 1] C) P ≠ 0

/-- (A12, stronger) The black times are not the zero set of a linear recurrence over `𝔽₂(x)`. -/
def NotZeroSetCharTwo : Prop :=
  ∀ (E : LinearRecurrence (RatFunc (ZMod 2))) (u : ℕ → RatFunc (ZMod 2)), E.IsSolution u →
    {t | u t = 0} ≠ {t | Rule30Prize.center t = true}

/-- (A7) Engel expansion of `x₂`: the remainders never vanish. -/
noncomputable abbrev x₂ : ℝ := ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1)

noncomputable def engelRem : ℕ → ℝ
  | 0 => x₂
  | n + 1 => if engelRem n = 0 then 0 else (⌈(engelRem n)⁻¹⌉ : ℝ) * engelRem n - 1

theorem problem1_iff_engel_infinite : Rule30Prize.Problem1 ↔ ∀ n, engelRem n ≠ 0 := sorry

/-- (fix) Diophantine graph of the center column: gives both colours, hence the ∀∃ form. -/
theorem center_diophFn :
    Dioph.DiophFn fun v : Fin 1 → ℕ => if Rule30Prize.center (v 0) then 1 else 0 := sorry

/-- (fix) `Problem1` via Mathlib's `List.HasPeriod` (Fine–Wilf file). -/
theorem problem1_iff_no_hasPeriod_tail : Rule30Prize.Problem1 ↔
    ¬ ∃ T P : ℕ, 0 < P ∧ ∀ n : ℕ,
      ((List.range n).map fun j => Rule30Prize.center (T + j)).HasPeriod P := sorry

/-- (fix) Filter form of eventual periodicity, for Mathlib's `∀ᶠ` API. -/
theorem problem1_iff_filter : Rule30Prize.Problem1 ↔
    ¬ ∃ P > 0, ∀ᶠ t in Filter.atTop, Rule30Prize.center (t + P) = Rule30Prize.center t := sorry

end CritiqueAdditions2
