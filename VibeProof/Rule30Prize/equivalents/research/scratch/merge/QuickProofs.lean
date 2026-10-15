import Rule30Equivalents
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.ModelTheory.Arithmetic.Presburger.Definability
import Mathlib.Dynamics.SymbolicDynamics.Basic

/-! Merged-catalog scratch: proofs of the cheapest corollaries, to calibrate the "few lines"
estimates in the catalog. Not part of any library. -/

open Ruliology.CellularAutomata

namespace CatalogProofs

noncomputable abbrev x₂ : ℝ := ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1)

theorem p1_iff_irr : Rule30Prize.Problem1 ↔ Irrational x₂ :=
  Rule30Equivalents.BinaryIrrational.problem1_iff_irrational_binary

/-- Continued fraction of `x₂` does not terminate. -/
theorem problem1_iff_cf_not_terminates : Rule30Prize.Problem1 ↔
    ¬ (GenContFract.of x₂).Terminates := by
  rw [p1_iff_irr, GenContFract.terminates_iff_rat, Irrational]
  constructor
  · rintro h ⟨q, hq⟩; exact h ⟨q, hq.symm⟩
  · rintro h ⟨q, hq⟩; exact h ⟨q, hq.symm⟩

/-- Infinitely many rationals `q` with `|x₂ - q| < 1 / den(q)²`. -/
theorem problem1_iff_dirichlet : Rule30Prize.Problem1 ↔
    {q : ℚ | |x₂ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  rw [p1_iff_irr, Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational]

/-- The integer multiples of `x₂` are dense in `ℝ / ℤ`. -/
theorem problem1_iff_dense_multiples : Rule30Prize.Problem1 ↔
    DenseRange (· • (x₂ : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ)) := by
  rw [AddCircle.denseRange_zsmul_coe_iff, div_one, p1_iff_irr]

/-- `x₂` has infinite order in `ℝ / ℤ`. -/
theorem problem1_iff_infinite_order : Rule30Prize.Problem1 ↔
    ¬ IsOfFinAddOrder (x₂ : AddCircle (1 : ℝ)) := by
  rw [AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div, div_one, p1_iff_irr, Irrational]
  constructor
  · intro h q hq; exact h ⟨q, hq⟩
  · rintro h ⟨q, hq⟩; exact h q hq

/-- Ultimately periodic sets, in Mathlib's form. -/
theorem ep_iff (f : ℕ → Bool) : Rule30Jen.EventuallyPeriodic f ↔
    ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ {t | f t = true} ↔ x + p ∈ {t | f t = true} := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun x hx => by simp only [Set.mem_setOf_eq, h x hx]⟩
  · rintro ⟨k, p, hp, h⟩
    refine ⟨k, p, hp, fun t ht => ?_⟩
    have := h t ht
    simp only [Set.mem_setOf_eq] at this
    cases h1 : f t <;> cases h2 : f (t + p) <;> simp_all

/-- Presburger non-definability (with any parameter set `A`). -/
theorem problem1_iff_not_presburger (A : Set ℕ) : Rule30Prize.Problem1 ↔
    ¬ A.Definable₁ FirstOrder.Language.presburger {t | Rule30Prize.center t = true} := by
  rw [FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic, ← ep_iff]; rfl

/-- The black times are not a semilinear set. -/
theorem problem1_iff_not_semilinear : Rule30Prize.Problem1 ↔
    ¬ IsSemilinearSet {t : ℕ | Rule30Prize.center t = true} := by
  rw [Nat.isSemilinearSet_iff_ultimately_periodic, ← ep_iff]; rfl

/-- The orbit closure in `{0,1}^ℕ` is infinite. -/
theorem problem1_iff_orbit_closure_infinite : Rule30Prize.Problem1 ↔
    (closure (Set.range fun n : ℕ => fun t => Rule30Prize.center (n + t))).Infinite := by
  rw [Rule30Equivalents.ShiftOrbit.problem1_iff_infinite_shifts]
  constructor
  · exact fun h => h.mono subset_closure
  · intro h hfin
    exact h (by rw [hfin.isClosed.closure_eq]; exact hfin)

/-- Mathlib's `SymbolicDynamics.FullShift.shift`: pairwise distinct shifts. -/
theorem problem1_iff_injective_fullShift : Rule30Prize.Problem1 ↔
    Function.Injective (fun n : ℕ => SymbolicDynamics.FullShift.shift n Rule30Prize.center) :=
  Rule30Equivalents.ShiftOrbit.problem1_iff_injective_shifts

/-- `Π⁰₂` normal form. -/
theorem problem1_iff_pi2 : Rule30Prize.Problem1 ↔
    ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ Rule30Prize.center (t + P) ≠ Rule30Prize.center t := by
  unfold Rule30Prize.Problem1 Rule30Jen.EventuallyPeriodic
  push Not
  rfl

namespace FC
def step (row : ℤ → Bool) : ℤ → Bool := fun i => xor (row (i - 1)) (row i || row (i + 1))
def state : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => step (state t)
def centerColumn (t : ℕ) : Bool := state t 0

theorem state_eq : ∀ t, state t = fun i => Rule30Jen.cell t i
  | 0 => rfl
  | t + 1 => by rw [state, state_eq t]; rfl

/-- The formal-conjectures statement is `Problem1`. -/
theorem problem1_iff_fc : Rule30Prize.Problem1 ↔
    ¬ ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t → centerColumn (t + p) = centerColumn t := by
  have hc : centerColumn = Rule30Prize.center := funext fun t => by
    rw [centerColumn, state_eq]; rfl
  rw [hc]
  constructor
  · rintro h ⟨p, hp, N, hN⟩; exact h ⟨N, p, hp, hN⟩
  · rintro h ⟨N, p, hp, hN⟩; exact h ⟨p, hp, N, hN⟩
end FC

end CatalogProofs

#print axioms CatalogProofs.problem1_iff_cf_not_terminates
#print axioms CatalogProofs.problem1_iff_dirichlet
#print axioms CatalogProofs.problem1_iff_dense_multiples
#print axioms CatalogProofs.problem1_iff_infinite_order
#print axioms CatalogProofs.problem1_iff_not_presburger
#print axioms CatalogProofs.problem1_iff_not_semilinear
#print axioms CatalogProofs.problem1_iff_orbit_closure_infinite
#print axioms CatalogProofs.problem1_iff_injective_fullShift
#print axioms CatalogProofs.problem1_iff_pi2
#print axioms CatalogProofs.FC.problem1_iff_fc
