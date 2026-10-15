import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30: the left half driven by a boundary column never absorbs

Scratch file (left-half / column-0 consistency angle).

`L c s t p` is the left half of rule 30 driven by an arbitrary boundary column `c` at position
`0`, started at time `0` from an arbitrary left-half state `s` (positions `p ≤ -1`):
`L (t+1) p = rule (L t (p-1)) (L t p) (L t (p+1))` for `p ≤ -1`, and `L t 0 = c t`.
(For `p ≥ 0` we simply store `c t`; only `p = 0` is ever read.)

* `edge`: if `s` has its leftmost black cell at `-m` (finite support), the leftmost black cell
  of `L t` is at `-(m + t)`.
* `no_periodic_adjacent`: two adjacent columns `i, i + 1` with `i + 1 ≤ 0` are never both
  eventually periodic.  With `i = -1`: **if the driver `c` is eventually periodic, column `-1` of
  the driven left half is not eventually periodic — for every finite-support nonzero start.**
  So there are no "absorbing words" on the left: a T-independent exclusion of a word via the left
  half can never come from column `-1` becoming eventually periodic.
* `no_periodic_column`: more generally, if `c` is eventually periodic then no column `-k`
  (`k ≥ 1`) of the driven left half is eventually periodic (strip + pigeonhole, as in Jen).
-/

namespace Ruliology.CellularAutomata
namespace Rule30DrivenLeft

open Rule30Jen

/-- The left half driven by the boundary column `c`, from left-half state `s` at time `0`. -/
def L (c : Nat → Bool) (s : Int → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then s p else c 0
  | t + 1, p => if p < 0 then rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) else c (t + 1)

variable {c : Nat → Bool} {s : Int → Bool}

theorem L_col0 (t : Nat) : L c s t 0 = c t := by
  cases t <;> simp [L]

theorem L_succ {t : Nat} {p : Int} (hp : p < 0) :
    L c s (t + 1) p = rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) := by
  simp [L, hp]

theorem L_zero {p : Int} (hp : p < 0) : L c s 0 p = s p := by
  simp [L, hp]

/-- Left permutivity inside the driven half (needs `p < 0`; at `p = 0` this is exactly the
consistency condition, which the driven half does not impose). -/
theorem L_left (t : Nat) {p : Int} (hp : p < 0) :
    L c s t (p - 1) = xor (L c s (t + 1) p) (L c s t p || L c s t (p + 1)) := by
  rw [L_succ hp]
  show L c s t (p - 1) = xor (xor (L c s t (p - 1)) (L c s t p || L c s t (p + 1)))
    (L c s t p || L c s t (p + 1))
  cases L c s t (p - 1) <;> cases L c s t p <;> cases L c s t (p + 1) <;> rfl

/-- The left edge moves left one cell per step. -/
theorem edge {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false) (hs1 : s (-(m : Int)) = true)
    (hm : 0 < m) :
    ∀ t : Nat, (∀ p : Int, p < -((m + t : Nat) : Int) → L c s t p = false) ∧
      L c s t (-((m + t : Nat) : Int)) = true := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [L_zero (by omega)]; exact hs0 p (by omega)
    · rw [L_zero (by omega)]; simpa using hs1
  | succ t ih =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [L_succ (by omega), ih.1 (p - 1) (by omega), ih.1 p (by omega), ih.1 (p + 1) (by omega)]
      rfl
    · rw [L_succ (by omega), ih.1 _ (by omega), ih.1 _ (by omega),
        show -(((m + (t + 1) : Nat)) : Int) + 1 = -((m + t : Nat) : Int) by omega, ih.2]
      rfl

theorem periodic_left {T P : Nat} {i : Int} (hi : i < 0)
    (h0 : ∀ t, T ≤ t → L c s (t + P) i = L c s t i)
    (h1 : ∀ t, T ≤ t → L c s (t + P) (i + 1) = L c s t (i + 1)) :
    ∀ t, T ≤ t → L c s (t + P) (i - 1) = L c s t (i - 1) := by
  intro t ht
  rw [L_left _ hi, L_left t hi, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

/-- Two adjacent periodic columns `i, i+1` (with `i < 0`) make every column to their left periodic. -/
theorem periodic_left_all {T P : Nat} {i : Int} (hi : i < 0)
    (h0 : ∀ t, T ≤ t → L c s (t + P) i = L c s t i)
    (h1 : ∀ t, T ≤ t → L c s (t + P) (i + 1) = L c s t (i + 1)) :
    ∀ n : Nat, (∀ t, T ≤ t → L c s (t + P) (i - n) = L c s t (i - n)) ∧
      ∀ t, T ≤ t → L c s (t + P) (i - n + 1) = L c s t (i - n + 1) := by
  intro n
  induction n with
  | zero => simpa using ⟨h0, h1⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · have := periodic_left (by omega) ih.1 ih.2
      rwa [show i - (n : Int) - 1 = i - ((n + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((n + 1 : Nat) : Int) + 1 = i - (n : Int) by omega]
      exact ih.1

/-- Far to the left, the edge reaches every column once: no column there is periodic. -/
theorem no_left_periodic {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ n : Nat, ∀ t, T ≤ t → L c s (t + P) (i - n) = L c s t (i - n)) : False := by
  -- a column q ≤ i with q ≤ -(m + T + P) - 1
  let q : Int := min i (-((m + T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ -((m + T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  -- the edge is at column q at time t₁ = -q - m
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = -q - m := ⟨(-q - m).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : L c s t₁ q = true := by
    have := (edge (c := c) hs0 hs1 hm t₁).2
    rwa [show -((m + t₁ : Nat) : Int) = q by omega] at this
  have hwhite : L c s (t₁ - P) q = false :=
    (edge (c := c) hs0 hs1 hm (t₁ - P)).1 q (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

/-- **Adjacent columns.** In the driven left half (finite-support nonzero start), two adjacent
columns `i, i + 1` with `i + 1 ≤ 0` are never both eventually periodic. -/
theorem no_periodic_adjacent {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) {i : Int} (hi : i < 0)
    (h0 : EventuallyPeriodic fun t => L c s t i)
    (h1 : EventuallyPeriodic fun t => L c s t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact no_left_periodic hs0 hs1 hm hP fun n => (periodic_left_all hi hp0 hp1 n).1

/-- **No left absorption.** If the driver `c` is eventually periodic, column `-1` of the driven
left half is not eventually periodic, whatever the (finite-support, nonzero) start state. -/
theorem col_neg_one_not_periodic {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) (hc : EventuallyPeriodic c) :
    ¬ EventuallyPeriodic fun t => L c s t (-1) := by
  intro hx
  refine no_periodic_adjacent hs0 hs1 hm (i := -1) (by omega) hx ?_
  obtain ⟨T, P, hP, h⟩ := hc
  exact ⟨T, P, hP, fun t ht => by simp only [show (-1 : Int) + 1 = 0 by omega, L_col0]; exact h t ht⟩

/-! ### Non-adjacent columns: the strip between column `j` and column `k ≤ 0` -/

/-- The cells strictly between columns `j` and `k` at step `t`. -/
def strip (c : Nat → Bool) (s : Int → Bool) (j k : Int) (t : Nat) : List Bool :=
  (List.range (k - j - 1).toNat).map fun (r : Nat) => L c s t (j + 1 + (r : Int))

set_option linter.unusedSimpArgs false in
theorem strip_agree {j k : Int} (hjk : j < k) (hk : k ≤ 0) {t₁ t₂ : Nat}
    (hs : strip c s j k t₁ = strip c s j k t₂)
    (hb : ∀ r, L c s (t₁ + r) j = L c s (t₂ + r) j ∧ L c s (t₁ + r) k = L c s (t₂ + r) k) :
    ∀ r, ∀ i, j ≤ i → i ≤ k → L c s (t₁ + r) i = L c s (t₂ + r) i := by
  intro r
  induction r with
  | zero =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb 0).1
    by_cases e2 : i = k
    · subst e2; exact (hb 0).2
    have := congrArg (fun l => l.getD (i - j - 1).toNat false) hs
    simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show (i - j - 1).toNat < (k - j - 1).toNat by omega),
      Option.map_some, Option.getD_some] at this
    rwa [show j + 1 + (((i - j - 1).toNat : Nat) : Int) = i by omega] at this
  | succ r ih =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb (r + 1)).1
    by_cases e2 : i = k
    · subst e2; exact (hb (r + 1)).2
    rw [show t₁ + (r + 1) = (t₁ + r) + 1 by omega, show t₂ + (r + 1) = (t₂ + r) + 1 by omega,
      L_succ (by omega), L_succ (by omega)]
    rw [ih (i - 1) (by omega) (by omega), ih i (by omega) (by omega), ih (i + 1) (by omega) (by omega)]

theorem between_periodic {j k : Int} (hjk : j + 1 < k) (hk : k ≤ 0)
    (hj : EventuallyPeriodic fun t => L c s t j) (hk' : EventuallyPeriodic fun t => L c s t k) :
    EventuallyPeriodic fun t => L c s t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk'
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip c s j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have key := strip_agree (by omega) hk he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1)
    (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by
        rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => L c s t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => L c s t k) hpk (n - m) _ (by omega)).symm

/-- **No column of the driven left half is eventually periodic** when the driver is eventually
periodic (finite-support nonzero start). -/
theorem no_periodic_column {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) (hc : EventuallyPeriodic c) {q : Int} (hq : q < 0)
    (hcol : EventuallyPeriodic fun t => L c s t q) : False := by
  have hc' : EventuallyPeriodic fun t => L c s t 0 := by
    obtain ⟨T, P, hP, h⟩ := hc
    exact ⟨T, P, hP, fun t ht => by simp only [L_col0]; exact h t ht⟩
  by_cases hadj : q = -1
  · subst hadj
    exact no_periodic_adjacent hs0 hs1 hm (i := -1) (by omega) hcol
      (by simpa [show (-1 : Int) + 1 = 0 by omega] using hc')
  · have hnext := between_periodic (j := q) (k := 0) (by omega) (Int.le_refl _) hcol hc'
    exact no_periodic_adjacent hs0 hs1 hm (i := q) hq hcol hnext


/-! ### Bridge to the real pattern -/

/-- The real rule 30 left half from time `T` on is the left half driven by the real center column
from the real row at time `T`. -/
theorem cell_eq_L (T : Nat) : ∀ k : Nat, ∀ p : Int, p ≤ 0 →
    L (fun k => cell (T + k) 0) (fun p => cell T p) k p = cell (T + k) p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · rw [L_zero h]; rfl
    · rw [show p = 0 by omega, L_col0]
  | succ k ih =>
    intro p hp
    by_cases h : p < 0
    · rw [L_succ h, ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      rfl
    · rw [show p = 0 by omega, L_col0]

/-- The real left half at time `T ≥ 1` is edge-structured with edge at `-T`. -/
theorem real_edge (T : Nat) :
    (∀ p : Int, p < -((T : Nat) : Int) → cell T p = false) ∧ cell T (-((T : Nat) : Int)) = true :=
  ⟨fun p hp => cell_eq_false_of_lt T p hp, cell_left_edge T⟩

end Rule30DrivenLeft
end Ruliology.CellularAutomata

#print axioms Ruliology.CellularAutomata.Rule30DrivenLeft.col_neg_one_not_periodic
