import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Fintype.Pigeonhole

/-! Scratch check (not part of any library): over any field `K`, Problem 1 holds iff the
center column, read as a sequence of `0`s and `1`s in `K`, satisfies no linear recurrence
(Mathlib's `LinearRecurrence.IsSolution`). Over `ZMod 2` this is "infinite linear complexity"
(Berlekamp–Massey). Definitions copied from `Rule30Jen` / `Rule30Prize`. -/

namespace R30Test

def rule (a b c : Bool) : Bool := xor a (b || c)

def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))

def center (t : Nat) : Bool := cell t 0

def EventuallyPeriodic (f : Nat → Bool) : Prop :=
  ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

def Problem1 : Prop := ¬ EventuallyPeriodic center

variable {K : Type*} [Field K]

/-- The sequence `f` read in `K`. -/
def toK (f : Nat → Bool) (n : Nat) : K := if f n then 1 else 0

theorem toK_inj {f g : Nat → Bool} {m n : Nat} (h : (toK f m : K) = toK g n) : f m = g n := by
  unfold toK at h
  cases hf : f m <;> cases hg : g n <;> simp_all

/-- An eventually periodic sequence satisfies a linear recurrence (order `T + P`). -/
theorem exists_recurrence_of_eventuallyPeriodic {f : Nat → Bool} (h : EventuallyPeriodic f) :
    ∃ E : LinearRecurrence K, E.IsSolution (toK f) := by
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨⟨T + P, fun i => if (i : Nat) = T then 1 else 0⟩, fun n => ?_⟩
  have hsum : (∑ i : Fin (T + P), (if (i : Nat) = T then (1 : K) else 0) * toK f (n + i))
      = toK f (n + T) := by
    rw [Finset.sum_eq_single (⟨T, by omega⟩ : Fin (T + P))]
    · simp
    · intro b _ hb
      have : (b : Nat) ≠ T := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  simp only
  rw [hsum]
  unfold toK
  rw [show n + (T + P) = (n + T) + P by omega, hper (n + T) (by omega)]

/-- A `0/1` sequence satisfying a linear recurrence over a field is eventually periodic. -/
theorem eventuallyPeriodic_of_recurrence {f : Nat → Bool} (E : LinearRecurrence K)
    (hE : E.IsSolution (toK f)) : EventuallyPeriodic f := by
  let g : Nat → (Fin E.order → Bool) := fun n i => f (n + i)
  obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  -- all later values agree
  have key : ∀ m, f (i + m) = f (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < E.order
      · have := congrFun hg ⟨m, hm⟩
        simpa [g] using this
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + E.order := ⟨m - E.order, by omega⟩
        apply toK_inj (K := K)
        have hi := hE (i + m')
        have hj := hE (j + m')
        rw [show i + (m' + E.order) = i + m' + E.order by omega,
          show j + (m' + E.order) = j + m' + E.order by omega, hi, hj]
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        unfold toK
        have := ih (m' + k) (by omega)
        rw [show i + m' + (k : Nat) = i + (m' + k) by omega,
          show j + m' + (k : Nat) = j + (m' + k) by omega, this]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨i, j - i, by omega, fun t ht => ?_⟩
    have := key (t - i)
    rw [show i + (t - i) = t by omega, show j + (t - i) = t + (j - i) by omega] at this
    exact this.symm
  · refine ⟨j, i - j, by omega, fun t ht => ?_⟩
    have := key (t - j)
    rw [show j + (t - j) = t by omega, show i + (t - j) = t + (i - j) by omega] at this
    exact this

/-- **Problem 1 ⟺ no linear recurrence over `K`** (for any field `K`, e.g. `ZMod 2` or `ℚ`). -/
theorem problem1_iff_no_recurrence :
    Problem1 ↔ ∀ E : LinearRecurrence K, ¬ E.IsSolution (toK center) := by
  constructor
  · intro h E hE
    exact h (eventuallyPeriodic_of_recurrence E hE)
  · intro h hp
    obtain ⟨E, hE⟩ := exists_recurrence_of_eventuallyPeriodic (K := K) hp
    exact h E hE

end R30Test

#print axioms R30Test.problem1_iff_no_recurrence
