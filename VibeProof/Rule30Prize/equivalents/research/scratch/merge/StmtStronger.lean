import Rule30Equivalents
import Ruliology.CellularAutomata.Rule30Realization

/-! Merged-catalog scratch: stronger and weaker statements (definitions only). -/

open Ruliology.CellularAutomata

namespace Catalog.Stronger

/-- No column of the single-seed pattern is eventually periodic. -/
def NoColumnPeriodic : Prop := ∀ j : ℤ, ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Jen.cell t j)

/-- Every nonzero finite row has no eventually periodic column (Jen–Kopra–Condrey setting). -/
def FinConf : Prop :=
  ∀ x : ℤ → Bool, (∃ W : ℕ, ∀ p : ℤ, W < p.natAbs → x p = false) → (∃ p, x p = true) →
    ∀ j : ℤ, ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Realization.evol x t j)

/-- The effective boundary `c(t) ∧ c(t+1)` seen by the left half is not eventually periodic. -/
def EffectiveBoundaryAperiodic : Prop :=
  ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Prize.center t && Rule30Prize.center (t + 1))

/-- Every finite word occurs in the center column. -/
def Disjunctive : Prop :=
  ∀ w : List Bool, ∃ i : ℕ, ∀ j : Fin w.length, Rule30Prize.center (i + (j : ℕ)) = w.get j

/-- Arbitrarily long white runs occur. -/
def UnboundedWhiteRuns : Prop := ∀ n : ℕ, ∃ i : ℕ, ∀ j < n, Rule30Prize.center (i + j) = false

/-- No residue class is eventually constant (anti-Toeplitz). -/
def AntiToeplitz : Prop :=
  ∀ P r : ℕ, 0 < P → r < P → ¬ ∃ K b, ∀ k, K ≤ k → Rule30Prize.center (r + k * P) = b

/-- A `Π⁰₁` strengthening: a disagreement within `3 log₂(T + P + 1)` steps. -/
def DefectBound : Prop :=
  ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ t ≤ T + 3 * Nat.log 2 (T + P + 1) ∧
    Rule30Prize.center (t + P) ≠ Rule30Prize.center t

/-! Weaker statements -/

/-- No eventual period `P` (for one fixed `P`). -/
def NoPer (P : ℕ) : Prop := ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t

/-- Not purely periodic. -/
def NotPurelyPeriodic : Prop := ∀ P, 0 < P → ∃ t, Rule30Prize.center (t + P) ≠ Rule30Prize.center t

/-- No eventual period that is a power of two. -/
def NoTwoPowerPeriod : Prop := ∀ k : ℕ, NoPer (2 ^ k)

example : NoColumnPeriodic → Rule30Prize.Problem1 := fun h => h 0
example : Rule30Prize.Problem1 → NoPer 1 := fun h ⟨T, hT⟩ => h ⟨T, 1, Nat.one_pos, hT⟩

end Catalog.Stronger
