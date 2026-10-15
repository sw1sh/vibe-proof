import Ruliology.CellularAutomata.Rule30Prize
import Ruliology.CellularAutomata.Rule30Realization
import Ruliology.CellularAutomata.Rule30Diagonals

/-!
Scratch (r30equiv / ca-structure): equivalent forms of Rule 30 Prize Problem 1 coming from the
symmetry class of rule 30 and from other finite seeds with the same center column.
-/

namespace R30EquivScratch
open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize

/-! ### Eventual periodicity is invariant under complement -/

theorem ep_not_iff (f : Nat → Bool) :
    EventuallyPeriodic (fun t => !f t) ↔ EventuallyPeriodic f := by
  constructor
  · rintro ⟨T, P, hP, h⟩
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h1 : (!f (t + P)) = !f t := h t ht
    revert h1
    cases f (t + P) <;> cases f t <;> simp
  · rintro ⟨T, P, hP, h⟩
    exact ⟨T, P, hP, fun t ht => by simp only [h t ht]⟩

/-! ### Mirror image: rule 86 from a single black cell -/

/-- Rule 86: `right xor (left || center)`, the left-right mirror image of rule 30. -/
def rule86 (a b c : Bool) : Bool := xor c (a || b)

def cell86 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule86 (cell86 t (p - 1)) (cell86 t p) (cell86 t (p + 1))

theorem cell86_eq : ∀ (t : Nat) (p : Int), cell86 t p = cell t (-p)
  | 0, p => by
    show decide (p = 0) = decide (-p = 0)
    by_cases h : p = 0
    · subst h; rfl
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  | t + 1, p => by
    show rule86 (cell86 t (p - 1)) (cell86 t p) (cell86 t (p + 1)) =
      rule (cell t (-p - 1)) (cell t (-p)) (cell t (-p + 1))
    rw [cell86_eq t (p - 1), cell86_eq t p, cell86_eq t (p + 1),
      show -(p - 1) = -p + 1 by omega, show -(p + 1) = -p - 1 by omega]
    cases cell t (-p + 1) <;> cases cell t (-p) <;> cases cell t (-p - 1) <;> rfl

theorem center86 (t : Nat) : cell86 t 0 = center t := by
  rw [cell86_eq]; rfl

theorem problem1_iff_86 : Problem1 ↔ ¬ EventuallyPeriodic (fun t => cell86 t 0) := by
  have : (fun t => cell86 t 0) = center := funext center86
  rw [this]; exact Iff.rfl

/-! ### Complement conjugates: rules 135 and 149 from a single white cell on a black background -/

/-- Rule 135: `!left xor (center && right)`. -/
def rule135 (a b c : Bool) : Bool := xor (!a) (b && c)
/-- Rule 149: `!right xor (center && left)`, the mirror image of rule 135. -/
def rule149 (a b c : Bool) : Bool := xor (!c) (b && a)

def cell135W : Nat → Int → Bool
  | 0, p => !decide (p = 0)
  | t + 1, p => rule135 (cell135W t (p - 1)) (cell135W t p) (cell135W t (p + 1))

def cell149W : Nat → Int → Bool
  | 0, p => !decide (p = 0)
  | t + 1, p => rule149 (cell149W t (p - 1)) (cell149W t p) (cell149W t (p + 1))

theorem cell135W_eq : ∀ (t : Nat) (p : Int), cell135W t p = !cell t p
  | 0, p => rfl
  | t + 1, p => by
    show rule135 (cell135W t (p - 1)) (cell135W t p) (cell135W t (p + 1)) =
      !rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
    rw [cell135W_eq t (p - 1), cell135W_eq t p, cell135W_eq t (p + 1)]
    cases cell t (p - 1) <;> cases cell t p <;> cases cell t (p + 1) <;> rfl

theorem cell149W_eq : ∀ (t : Nat) (p : Int), cell149W t p = !cell t (-p)
  | 0, p => by
    show (!decide (p = 0)) = !decide (-p = 0)
    by_cases h : p = 0
    · subst h; rfl
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  | t + 1, p => by
    show rule149 (cell149W t (p - 1)) (cell149W t p) (cell149W t (p + 1)) =
      !rule (cell t (-p - 1)) (cell t (-p)) (cell t (-p + 1))
    rw [cell149W_eq t (p - 1), cell149W_eq t p, cell149W_eq t (p + 1),
      show -(p - 1) = -p + 1 by omega, show -(p + 1) = -p - 1 by omega]
    cases cell t (-p + 1) <;> cases cell t (-p) <;> cases cell t (-p - 1) <;> rfl

theorem problem1_iff_135W : Problem1 ↔ ¬ EventuallyPeriodic (fun t => cell135W t 0) := by
  have : (fun t => cell135W t 0) = (fun t => !center t) := by
    funext t; rw [cell135W_eq]; rfl
  rw [this, ep_not_iff]; exact Iff.rfl

theorem problem1_iff_149W : Problem1 ↔ ¬ EventuallyPeriodic (fun t => cell149W t 0) := by
  have : (fun t => cell149W t 0) = (fun t => !center t) := by
    funext t; rw [cell149W_eq]; rfl
  rw [this, ep_not_iff]; exact Iff.rfl

/-! ### Jen makes "Problem 1 ⟺ (same question for another column)" as hard as both -/

theorem iff_iff_and_of_or {A B : Prop} (h : A ∨ B) : (A ↔ B) ↔ (A ∧ B) := by
  constructor
  · intro e
    rcases h with a | b
    · exact ⟨a, e.1 a⟩
    · exact ⟨e.2 b, b⟩
  · rintro ⟨a, b⟩
    exact ⟨fun _ => b, fun _ => a⟩

theorem problem1_or_column (j : Int) (hj : j ≠ 0) :
    Problem1 ∨ ¬ EventuallyPeriodic (fun t => cell t j) := by
  by_cases h : Problem1
  · exact Or.inl h
  · refine Or.inr fun hjp => ?_
    have hc : EventuallyPeriodic center := Classical.byContradiction h
    exact jen 0 j (Ne.symm hj) ⟨hc, hjp⟩

/-- Any proof that Problem 1 is equivalent to the same question for column `j ≠ 0` would prove
both statements. -/
theorem problem1_iff_column_iff_both (j : Int) (hj : j ≠ 0) :
    (Problem1 ↔ ¬ EventuallyPeriodic (fun t => cell t j)) ↔
      (Problem1 ∧ ¬ EventuallyPeriodic (fun t => cell t j)) :=
  iff_iff_and_of_or (problem1_or_column j hj)

/-! ### The inverse problem: the center column determines the left half -/

open Rule30Realization in
/-- **Problem 1 as an inverse problem.** With the right half white, every column `u` is realized by
exactly one configuration `conf seed u`; Problem 1 says that no eventually periodic `u` is realized
by the single seed. -/
theorem problem1_iff_realization :
    Problem1 ↔ ∀ u : Nat → Bool, EventuallyPeriodic u → conf seed u ≠ seed := by
  constructor
  · intro h u hu he
    apply h
    have : center = u := by
      funext t
      have h1 := (realize seed u).2 t
      rw [he, evol_seed] at h1
      exact h1
    rw [this]; exact hu
  · intro h hc
    have hs : conf seed center = seed := by
      symm
      refine unique (fun p hp => ((realize seed center).1 p hp).symm) (fun t => ?_)
      rw [evol_seed, (realize seed center).2 t]; rfl
    exact h center hc hs

/-! ### Stripe seeds: `1`, `11`, `101`, `1011`, `10101`, … have the center column of the seed -/

theorem cell_diag (t : Nat) : cell t (t : Int) = true := by
  have h := Rule30Diagonals.R_zero t
  unfold Rule30Diagonals.R at h
  exact (Rule30Diagonals.cell_congr (by omega)).trans h

theorem cell_subdiag : ∀ t : Nat, cell t ((t : Int) - 1) = decide (t % 2 = 1)
  | 0 => by decide
  | t + 1 => by
    have h := Rule30Diagonals.R_one_succ t
    unfold Rule30Diagonals.R at h
    rw [Rule30Diagonals.cell_congr (show ((t + 1 : Nat) : Int) - 1 =
        ((t + 1 : Nat) : Int) - ((1 : Nat) : Int) by omega), h,
      Rule30Diagonals.cell_congr (show (t : Int) - ((1 : Nat) : Int) = (t : Int) - 1 by omega),
      cell_subdiag t]
    by_cases ht : t % 2 = 1
    · rw [decide_eq_true ht, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false ht, decide_eq_true (by omega)]; rfl

/-- The seed with black cells at the even positions of `[0, n)` and at `n`:
`n = 0, 1, 2, 3, 4, …` gives `1, 11, 101, 1011, 10101, …`. -/
def stripeSeed (n : Nat) (p : Int) : Bool :=
  decide (0 ≤ p ∧ p < n ∧ p % 2 = 0) || decide (p = n)

/-- The pattern grown from `stripeSeed n`: the single-seed pattern left of the diagonal `p = t`,
the fixed stripe (black at even positions) on `[t, t + n)`, and the right edge at `t + n`. -/
def pat (n t : Nat) (p : Int) : Bool :=
  if p < t then cell t p
  else if p < (t : Int) + n then decide (p % 2 = 0)
  else decide (p = (t : Int) + n)

theorem pat_left {n t : Nat} {p : Int} (h : p < (t : Int)) : pat n t p = cell t p := by
  unfold pat; rw [if_pos h]

theorem pat_band {n t : Nat} {p : Int} (h1 : (t : Int) ≤ p) (h2 : p < (t : Int) + n) :
    pat n t p = decide (p % 2 = 0) := by
  unfold pat; rw [if_neg (show ¬ p < (t : Int) by omega), if_pos h2]

theorem pat_edge {n t : Nat} {p : Int} (h : (t : Int) + n ≤ p) :
    pat n t p = decide (p = (t : Int) + n) := by
  unfold pat
  rw [if_neg (show ¬ p < (t : Int) by omega), if_neg (show ¬ p < (t : Int) + n by omega)]

/-- Inside the stripe, or at its right end, one of a cell and its right neighbour is black. -/
theorem pat_or {n t : Nat} {p : Int} (h1 : (t : Int) ≤ p) (h2 : p ≤ (t : Int) + n) :
    (pat n t p || pat n t (p + 1)) = true := by
  by_cases hn : p < (t : Int) + n
  · rw [pat_band h1 hn]
    by_cases hp : p % 2 = 0
    · rw [decide_eq_true hp]; rfl
    · rw [decide_eq_false hp]
      by_cases hn' : p + 1 < (t : Int) + n
      · rw [pat_band (by omega) hn', decide_eq_true (show (p + 1) % 2 = 0 by omega)]; rfl
      · rw [pat_edge (show (t : Int) + n ≤ p + 1 by omega),
          decide_eq_true (show p + 1 = (t : Int) + n by omega)]; rfl
  · rw [pat_edge (show (t : Int) + n ≤ p by omega), decide_eq_true (show p = (t : Int) + n by omega)]
    rfl

open Rule30Realization in
theorem evol_stripeSeed (n : Nat) : ∀ (t : Nat) (p : Int), evol (stripeSeed n) t p = pat n t p
  | 0, p => by
    show stripeSeed n p = pat n 0 p
    unfold stripeSeed
    rcases (show p < 0 ∨ (0 ≤ p ∧ p < n) ∨ (n : Int) ≤ p by omega) with h | ⟨h1, h2⟩ | h
    · rw [pat_left (show p < ((0 : Nat) : Int) by omega),
        decide_eq_false (show ¬ (0 ≤ p ∧ p < (n : Int) ∧ p % 2 = 0) by omega),
        decide_eq_false (show ¬ p = (n : Int) by omega)]
      show false = decide (p = 0)
      rw [decide_eq_false (show ¬ p = 0 by omega)]
    · rw [pat_band (show ((0 : Nat) : Int) ≤ p by omega) (show p < ((0 : Nat) : Int) + n by omega),
        decide_eq_false (show ¬ p = (n : Int) by omega)]
      by_cases hp : p % 2 = 0
      · rw [decide_eq_true (show 0 ≤ p ∧ p < (n : Int) ∧ p % 2 = 0 from ⟨h1, h2, hp⟩),
          decide_eq_true hp]; rfl
      · rw [decide_eq_false (show ¬ (0 ≤ p ∧ p < (n : Int) ∧ p % 2 = 0) by omega),
          decide_eq_false hp]; rfl
    · rw [pat_edge (show ((0 : Nat) : Int) + n ≤ p by omega),
        decide_eq_false (show ¬ (0 ≤ p ∧ p < (n : Int) ∧ p % 2 = 0) by omega)]
      by_cases he : p = (n : Int)
      · rw [decide_eq_true he, decide_eq_true (show p = ((0 : Nat) : Int) + n by omega)]; rfl
      · rw [decide_eq_false he, decide_eq_false (show ¬ p = ((0 : Nat) : Int) + n by omega)]; rfl
  | t + 1, p => by
    show rule (evol (stripeSeed n) t (p - 1)) (evol (stripeSeed n) t p)
        (evol (stripeSeed n) t (p + 1)) = pat n (t + 1) p
    rw [evol_stripeSeed n t (p - 1), evol_stripeSeed n t p, evol_stripeSeed n t (p + 1)]
    rcases (show p + 1 < t ∨ p + 1 = t ∨ p = t ∨ ((t : Int) + 1 ≤ p ∧ p < (t : Int) + 1 + n) ∨
        (t : Int) + 1 + n ≤ p by omega) with h | h | h | ⟨h1, h2⟩ | h
    · -- all three neighbours lie left of the diagonal
      rw [pat_left (show p - 1 < (t : Int) by omega), pat_left (show p < (t : Int) by omega),
        pat_left (show p + 1 < (t : Int) by omega), pat_left (show p < ((t + 1 : Nat) : Int) by omega)]
      rfl
    · -- p = t - 1: the right neighbour is on the diagonal
      rw [pat_left (show p - 1 < (t : Int) by omega), pat_left (show p < (t : Int) by omega),
        pat_left (show p < ((t + 1 : Nat) : Int) by omega)]
      have hsub : cell t p = decide (t % 2 = 1) := by
        rw [Rule30Diagonals.cell_congr (show p = (t : Int) - 1 by omega), cell_subdiag]
      have hdiag : cell t (p + 1) = true := by
        rw [Rule30Diagonals.cell_congr (show p + 1 = (t : Int) by omega), cell_diag]
      have key : (cell t p || pat n t (p + 1)) = (cell t p || cell t (p + 1)) := by
        rw [hdiag, hsub]
        by_cases ht : t % 2 = 1
        · rw [decide_eq_true ht]; rfl
        · rw [decide_eq_false ht]
          by_cases hn : p + 1 < (t : Int) + n
          · rw [pat_band (show (t : Int) ≤ p + 1 by omega) hn,
              decide_eq_true (show (p + 1) % 2 = 0 by omega)]
          · rw [pat_edge (show (t : Int) + n ≤ p + 1 by omega),
              decide_eq_true (show p + 1 = (t : Int) + n by omega)]
      show xor (cell t (p - 1)) (cell t p || pat n t (p + 1)) =
        xor (cell t (p - 1)) (cell t p || cell t (p + 1))
      rw [key]
    · -- p = t: the cell just left of the stripe
      rw [pat_left (show p - 1 < (t : Int) by omega), pat_left (show p < ((t + 1 : Nat) : Int) by omega)]
      have hor := pat_or (n := n) (t := t) (p := p) (by omega) (by omega)
      show xor (cell t (p - 1)) (pat n t p || pat n t (p + 1)) = cell (t + 1) p
      rw [hor]
      have hsub : cell t (p - 1) = decide (t % 2 = 1) := by
        rw [Rule30Diagonals.cell_congr (show p - 1 = (t : Int) - 1 by omega), cell_subdiag]
      have hsub' : cell (t + 1) p = decide ((t + 1) % 2 = 1) := by
        rw [Rule30Diagonals.cell_congr (show p = ((t + 1 : Nat) : Int) - 1 by omega), cell_subdiag]
      rw [hsub, hsub']
      by_cases ht : t % 2 = 1
      · rw [decide_eq_true ht, decide_eq_false (show ¬ (t + 1) % 2 = 1 by omega)]; rfl
      · rw [decide_eq_false ht, decide_eq_true (show (t + 1) % 2 = 1 by omega)]; rfl
    · -- inside the stripe
      rw [pat_band (show (t : Int) ≤ p - 1 by omega) (show p - 1 < (t : Int) + n by omega),
        pat_band (show ((t + 1 : Nat) : Int) ≤ p by omega) (show p < ((t + 1 : Nat) : Int) + n by omega)]
      have hor := pat_or (n := n) (t := t) (p := p) (by omega) (by omega)
      show xor (decide ((p - 1) % 2 = 0)) (pat n t p || pat n t (p + 1)) = decide (p % 2 = 0)
      rw [hor]
      by_cases hp : p % 2 = 0
      · rw [decide_eq_false (show ¬ (p - 1) % 2 = 0 by omega), decide_eq_true hp]; rfl
      · rw [decide_eq_true (show (p - 1) % 2 = 0 by omega), decide_eq_false hp]; rfl
    · -- at or right of the new right edge
      rw [pat_edge (show (t : Int) + n ≤ p - 1 by omega), pat_edge (show (t : Int) + n ≤ p by omega),
        pat_edge (show (t : Int) + n ≤ p + 1 by omega),
        pat_edge (show ((t + 1 : Nat) : Int) + n ≤ p by omega),
        decide_eq_false (show ¬ p = (t : Int) + n by omega),
        decide_eq_false (show ¬ p + 1 = (t : Int) + n by omega)]
      show xor (decide (p - 1 = (t : Int) + n)) false = decide (p = ((t + 1 : Nat) : Int) + n)
      by_cases he : p - 1 = (t : Int) + n
      · rw [decide_eq_true he, decide_eq_true (show p = ((t + 1 : Nat) : Int) + n by omega)]; rfl
      · rw [decide_eq_false he, decide_eq_false (show ¬ p = ((t + 1 : Nat) : Int) + n by omega)]; rfl

open Rule30Realization in
/-- **Every stripe seed has exactly the center column of the single seed.** -/
theorem stripeSeed_center (n t : Nat) : evol (stripeSeed n) t 0 = center t := by
  rw [evol_stripeSeed]
  cases t with
  | zero =>
    by_cases hn : (0 : Int) < ((0 : Nat) : Int) + n
    · rw [pat_band (by omega) hn]; rfl
    · rw [pat_edge (by omega), decide_eq_true (show (0 : Int) = ((0 : Nat) : Int) + n by omega)]; rfl
  | succ t => rw [pat_left (by omega)]; rfl

open Rule30Realization in
theorem problem1_iff_stripeSeed (n : Nat) :
    Problem1 ↔ ¬ EventuallyPeriodic (fun t => evol (stripeSeed n) t 0) := by
  have : (fun t => evol (stripeSeed n) t 0) = center := funext (stripeSeed_center n)
  rw [this]; exact Iff.rfl

end R30EquivScratch

#print axioms R30EquivScratch.problem1_iff_86
#print axioms R30EquivScratch.problem1_iff_135W
#print axioms R30EquivScratch.problem1_iff_149W
#print axioms R30EquivScratch.problem1_iff_column_iff_both
#print axioms R30EquivScratch.problem1_iff_realization
#print axioms R30EquivScratch.problem1_iff_stripeSeed
